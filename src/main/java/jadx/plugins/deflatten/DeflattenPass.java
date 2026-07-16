package jadx.plugins.deflatten;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.jetbrains.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import jadx.api.plugins.pass.JadxPassInfo;
import jadx.api.plugins.pass.impl.OrderedJadxPassInfo;
import jadx.api.plugins.pass.types.JadxDecompilePass;
import jadx.core.dex.attributes.AFlag;
import jadx.core.dex.attributes.AType;
import jadx.core.dex.attributes.nodes.PhiListAttr;
import jadx.core.dex.instructions.ConstStringNode;
import jadx.core.dex.instructions.InsnType;
import jadx.core.dex.instructions.PhiInsn;
import jadx.core.dex.instructions.SwitchInsn;
import jadx.core.dex.instructions.args.ArgType;
import jadx.core.dex.instructions.args.InsnArg;
import jadx.core.dex.instructions.args.InsnWrapArg;
import jadx.core.dex.instructions.args.RegisterArg;
import jadx.core.dex.instructions.args.SSAVar;
import jadx.core.dex.nodes.BlockNode;
import jadx.core.dex.nodes.ClassNode;
import jadx.core.dex.nodes.InsnNode;
import jadx.core.dex.nodes.MethodNode;
import jadx.core.dex.nodes.RootNode;
import jadx.core.dex.visitors.InitCodeVariables;
import jadx.core.dex.visitors.blocks.BlockProcessor;
import jadx.core.dex.visitors.blocks.BlockSplitter;
import jadx.core.dex.visitors.ssa.SSATransform;
import jadx.core.utils.BlockUtils;
import jadx.core.utils.InsnRemover;

/**
 * Detects a {@code while(true) switch(str.hashCode() ^ K)} flattening dispatcher and rebuilds the
 * real control-flow graph.
 *
 * <p>
 * The dispatcher is a loop whose header holds a phi for the {@code String} state variable; the
 * switch
 * (in the header or a straight-line successor) routes {@code state.hashCode() ^ K} to a case block,
 * and each case reassigns the state to advance. Because every state value is a compile-time
 * constant,
 * the executed sequence of case blocks is fully static. This pass:
 * <ol>
 * <li>walks the state phi tree to enumerate every {@code (state, case-block)} transition,
 * statically evaluating the selector (see {@link SelectorEval}), and groups the transitions by the
 * <b>target case block</b> they route to;</li>
 * <li>reconstructs every <i>other</i> loop-carried value (accumulators, cipher handles, loop
 * indices, ...): a merge phi is inserted at each target reached by several transitions, and each
 * read
 * is repointed to the value entering its target — found by reaching-definition (dominator walk) at
 * the transition source;</li>
 * <li>rewires each transition edge straight to its case block and deletes the dispatcher (header,
 * selector, switch, back-edge merges and the dead default).</li>
 * </ol>
 *
 * <p>
 * The transitions form a general reducible graph. A case that picks its next state by a runtime
 * condition ({@code str = cond ? "X" : "Y"}) becomes a real {@code if} with two direct edges; two
 * states advancing to a common third (reconvergence) or a state reached from both an initialiser
 * and
 * a back-edge (a loop) become a shared target block with several predecessors. For every such
 * shared
 * target the pass inserts a fresh merge phi per loop-carried variable, with one operand — resolved
 * by
 * reaching-definition at the edge source — per incoming edge, so accumulators/handles/loop indices
 * are rebuilt correctly (an unchanged value collapses back out via {@code simplifyPhi}). Nested
 * dispatchers are handled by the fixpoint in {@link #visit}: each round removes one dispatcher and
 * rescans.
 *
 * <p>
 * The whole plan is computed from pure reads and validated (the state graph is rooted and
 * reachable,
 * every edge delivers a resolvable value, every read is attributable to a state, and nothing
 * surviving depends on a to-be-deleted block) <b>before</b> any mutation, so an unrecognised shape
 * bails cleanly and never leaves a half-rewritten method. Merge phis get their code variable and
 * type
 * stamped explicitly since {@code InitCodeVariables}/type inference do not run again after this
 * pass.
 */
public class DeflattenPass implements JadxDecompilePass {

	private static final Logger LOG = LoggerFactory.getLogger(DeflattenPass.class);

	private final DeflattenOptions options;

	public DeflattenPass(DeflattenOptions options) {
		this.options = options;
	}

	@Override
	public JadxPassInfo getInfo() {
		return new OrderedJadxPassInfo("Deflatten", "Undo hashCode-switch control-flow flattening")
				.after("ReplaceNewArray")
				.before("RegionMakerVisitor");
	}

	@Override
	public void init(RootNode root) {
		// no-op
	}

	@Override
	public boolean visit(ClassNode cls) {
		return options.isEnabled();
	}

	@Override
	public void visit(MethodNode mth) {
		if (!options.isEnabled() || mth.isNoCode() || mth.contains(AType.JADX_ERROR)) {
			return;
		}
		int removed = 0;
		try {
			boolean changed = true;
			while (changed) {
				changed = false;
				for (BlockNode block : new ArrayList<>(mth.getBasicBlocks())) {
					Plan plan = plan(mth, block);
					if (plan != null) {
						apply(mth, plan);
						BlockProcessor.updateBlocksData(mth);
						removed++;
						changed = true;
						break; // CFG changed underneath us: restart the scan
					}
				}
			}
			if (removed > 0) {
				// merge phis we inserted have brand-new SSA vars with no code variable (InitCodeVariables
				// already ran before this pass). Give each new var a code variable, reconnecting its phi
				// component, without resetting the types the earlier type-inference pass computed.
				for (SSAVar v : new ArrayList<>(mth.getSVars())) {
					if (!v.isCodeVarSet()) {
						ArgType t = v.getTypeInfo().getType();
						InitCodeVariables.initCodeVar(v);
						// initCodeVar derives a code-var type only from immutable types; carry over the
						// concrete type we stamped on the new var so it is not left "unknown".
						if (t.isTypeKnown() && v.isCodeVarSet()) {
							ArgType ct = v.getCodeVar().getType();
							if (ct == null || !ct.isTypeKnown()) {
								v.getCodeVar().setType(t);
							}
						}
					}
				}
			}
		} catch (StackOverflowError | RuntimeException e) {
			LOG.warn("deflatten: skipped {}", mth, e);
			return;
		}
		if (removed > 0) {
			LOG.info("deflatten: removed {} dispatcher(s) in {}", removed, mth);
			if (options.isComments()) {
				mth.addInfoComment("Control-flow deflattened: " + removed + " dispatcher(s)");
			}
		}
	}

	// ---- planning (pure reads, no mutation) ---------------------------------------------------------

	private @Nullable Plan plan(MethodNode mth, BlockNode switchBlock) {
		SwitchInsn sw = (SwitchInsn) BlockUtils.getLastInsnWithType(switchBlock, InsnType.SWITCH);
		if (sw == null || sw.getArgsCount() < 1) {
			return null;
		}
		InsnArg selector = sw.getArg(0);
		SSAVar stateVar = SelectorEval.findHashCodeReceiver(selector);
		if (stateVar == null) {
			return bail("no single hashCode receiver");
		}
		// The state var (the header phi's result) is used by the hashCode selector and, in the real
		// two-phi dispatcher shape, also as the "state unchanged" default self-loop operand of the
		// back-edge merge phi. Both are dispatcher-internal and torn down with it; a use that escapes to
		// surviving code is caught later by safeToDelete. So no fixed use-count is required here.
		InsnNode stateAssign = stateVar.getAssignInsn();
		if (!(stateAssign instanceof PhiInsn)) {
			return bail("state var not a phi: " + stateAssign);
		}
		PhiInsn statePhi = (PhiInsn) stateAssign;
		Map<InsnNode, BlockNode> insnBlocks = indexInsnBlocks(mth);
		BlockNode headerBlock = insnBlocks.get(statePhi);
		if (headerBlock == null) {
			return bail("no header block for state phi");
		}
		// 1) enumerate state transitions by walking the (possibly nested) state phi tree. When the
		// selector folds an UNKNOWN constant (e.g. an unresolved androidx `SGET` in the XOR chain,
		// because those libraries are not loaded), SelectorEval can't evaluate it. But the selector is
		// still `hashCode(state) ^ M` for a fixed mask M, so derive M from the constraint that the state
		// strings map bijectively onto the case keys, and route by `hashCode(state) ^ M` instead.
		Integer xorMask = deriveXorMask(statePhi, stateVar, sw);
		List<Leaf> leaves = new ArrayList<>();
		if (!collectLeaves(statePhi, headerBlock, new ArrayList<>(), selector, stateVar, sw,
				switchBlock, headerBlock, insnBlocks, leaves, new IdentityHashMap<>(), xorMask)) {
			return bail("collectLeaves failed");
		}
		if (leaves.isEmpty()) {
			return bail("no leaves");
		}
		// 2) group transition edges by their TARGET case block. A target reached by several edges is a
		// merge — whether from the same next-state string (reconvergence), from init + a back-edge (a
		// loop), or from two states that route to the same block (a shared `case X: case Y:` body). Each
		// merge gets one phi per loop-carried variable.
		Map<BlockNode, List<Leaf>> edgesByTarget = new LinkedHashMap<>();
		Set<BlockNode> targets = new HashSet<>();
		for (Leaf leaf : leaves) {
			edgesByTarget.computeIfAbsent(leaf.target, k -> new ArrayList<>()).add(leaf);
			targets.add(leaf.target);
		}
		// 3) compute which blocks die once the transitions are rewired
		Set<BlockNode> dead = deadBlocks(mth, leaves);
		if (!dead.contains(switchBlock) || !dead.contains(headerBlock)) {
			return bail("dispatcher core not unreachable after rewire");
		}
		// 4) recover the transition graph over target blocks. An edge originates in the case body that
		// produced it (the block feeding the state phi, `redirectFrom`); the target case block dominating
		// that source is the predecessor node. An edge originating in a block dominated by no target is
		// an entry edge (the pre-header init). A conditional entry (`s = cond ? A : B` before the loop)
		// yields several entry edges/targets — allowed. Using redirectFrom (the real control-flow source)
		// rather than the constant's block is robust to constants hoisted through MOVEs/pass-throughs.
		Map<Leaf, BlockNode> predTargetOf = new IdentityHashMap<>();
		Set<BlockNode> entryTargets = new LinkedHashSet<>();
		for (Leaf leaf : leaves) {
			BlockNode pred = classifyTarget(leaf.redirectFrom, targets);
			predTargetOf.put(leaf, pred);
			if (pred == null) {
				entryTargets.add(leaf.target);
			}
		}
		if (entryTargets.isEmpty()) {
			return bail("no entry target");
		}
		if (!allTargetsReachable(entryTargets, edgesByTarget, predTargetOf)) {
			return bail("unreachable target in graph");
		}
		// each merge target needs one phi operand per predecessor: its incoming edges must come from
		// distinct, surviving blocks.
		for (List<Leaf> es : edgesByTarget.values()) {
			if (es.size() < 2) {
				continue;
			}
			Set<BlockNode> froms = new HashSet<>();
			for (Leaf leaf : es) {
				if (dead.contains(leaf.redirectFrom)) {
					return bail("merge edge from a dead block");
				}
				if (!froms.add(leaf.redirectFrom)) {
					return bail("two merge edges from one block");
				}
			}
		}
		// 5) plan each loop-carried variable (every header phi but the state phi). For each we record the
		// value it delivers on each edge (by reaching-def at the edge's source), the reads to repoint,
		// and a feasibility check that value resolution — with a merge phi inserted at each merge target
		// — terminates. Nothing is mutated here.
		List<CarriedVar> carried = new ArrayList<>();
		Set<RegisterArg> replacedUses = new HashSet<>();
		PhiListAttr headerPhis = headerBlock.get(AType.PHI_LIST);
		if (headerPhis != null) {
			for (PhiInsn carriedPhi : new ArrayList<>(headerPhis.getList())) {
				if (carriedPhi == statePhi) {
					continue;
				}
				RegisterArg rv = carriedPhi.getResult();
				if (rv == null || rv.getSVar() == null) {
					return bail("carried phi has no result");
				}
				SSAVar rvVar = rv.getSVar();
				Map<Leaf, RegisterArg> delivered = new IdentityHashMap<>();
				for (Leaf leaf : leaves) {
					RegisterArg v = reachingValue(rv.getRegNum(), leaf.redirectFrom, rvVar);
					if (v == null) {
						return bail("no reaching value for carried reg at an edge");
					}
					delivered.put(leaf, v);
				}
				if (!resolutionFeasible(edgesByTarget, delivered, predTargetOf, rvVar)) {
					return bail("carried value resolution does not terminate");
				}
				List<UseSite> uses = new ArrayList<>();
				for (RegisterArg use : new ArrayList<>(rvVar.getUseList())) {
					InsnNode useInsn = use.getParentInsn();
					BlockNode useBlock = useInsn == null ? null : insnBlocks.get(useInsn);
					if (useBlock == null) {
						return bail("carried use has no block");
					}
					if (dead.contains(useBlock)) {
						continue; // structural use inside the dispatcher, torn down with it
					}
					BlockNode target = classifyTarget(useBlock, targets);
					if (target == null) {
						return bail("carried read not attributable to a target");
					}
					uses.add(new UseSite(use, target));
					replacedUses.add(use);
				}
				carried.add(new CarriedVar(rv, delivered, uses));
			}
		}
		// 6) nothing surviving may depend on a value defined in a dead block beyond the reads we repoint
		if (!safeToDelete(dead, insnBlocks, replacedUses)) {
			return bail("a surviving value depends on a to-be-deleted block");
		}
		int shared = 0;
		for (List<Leaf> es : edgesByTarget.values()) {
			if (es.size() >= 2) {
				shared++;
			}
		}
		LOG.debug("deflatten: planned {} targets ({} merges), {} carried, {} dead in {}",
				edgesByTarget.size(), shared, carried.size(), dead.size(), mth);
		return new Plan(leaves, dead, edgesByTarget, predTargetOf, carried);
	}

	/**
	 * Derive the XOR mask {@code M} for a selector of the form {@code state.hashCode() ^ M} whose
	 * constants can't all be folded (an unresolved static field is XORed in). {@code M} is the value
	 * that maps every state string bijectively onto a distinct case key, so try {@code M = hashCode(s0)
	 * ^ k} for each key {@code k} and keep the one under which every state routes to a distinct valid
	 * key. Returns {@code null} when no such mask exists (the selector is not a pure XOR chain, or the
	 * constants are all known — in which case {@link SelectorEval} handles it directly).
	 */
	private @Nullable Integer deriveXorMask(PhiInsn statePhi, SSAVar stateVar, SwitchInsn sw) {
		Set<String> strings = new LinkedHashSet<>();
		collectStateStrings(statePhi, stateVar, new IdentityHashMap<>(), strings);
		int[] keys = sw.getKeys();
		if (strings.isEmpty() || keys == null || keys.length == 0) {
			return null;
		}
		Set<Integer> keySet = new HashSet<>();
		for (int k : keys) {
			keySet.add(k);
		}
		String first = strings.iterator().next();
		Integer found = null;
		for (int k : keys) {
			int m = first.hashCode() ^ k;
			Set<Integer> mapped = new HashSet<>();
			boolean ok = true;
			for (String s : strings) {
				int key = s.hashCode() ^ m;
				if (!keySet.contains(key) || !mapped.add(key)) {
					ok = false;
					break;
				}
			}
			if (ok) {
				if (found != null) {
					return null; // ambiguous: more than one mask yields a valid bijection — not safe
				}
				found = m;
			}
		}
		return found;
	}

	/** Collect every constant state string reachable through the (nested) state phi tree. */
	private void collectStateStrings(PhiInsn phi, SSAVar stateVar, IdentityHashMap<PhiInsn, Boolean> seen, Set<String> out) {
		if (seen.put(phi, Boolean.TRUE) != null) {
			return;
		}
		for (int i = 0; i < phi.getArgsCount(); i++) {
			RegisterArg op = phi.getArg(i);
			if (op.getSVar() == null) {
				continue;
			}
			InsnNode def = resolveThroughMoves(op.getSVar().getAssignInsn());
			if (def == stateVar.getAssignInsn()) {
				continue;
			}
			if (def instanceof ConstStringNode) {
				out.add(((ConstStringNode) def).getString());
			} else if (def instanceof PhiInsn) {
				collectStateStrings((PhiInsn) def, stateVar, seen, out);
			}
		}
	}

	/** Decline a candidate dispatcher; the reason is logged at DEBUG for diagnosing missed cases. */
	private static @Nullable Plan bail(String reason) {
		LOG.debug("deflatten: bail — {}", reason);
		return null;
	}

	/**
	 * Recursively enumerate the state phi tree. A constant-string operand is a transition leaf; a phi
	 * operand (a back-edge merge) is followed deeper. Any other operand means a non-constant state
	 * (e.g. a real conditional transition), which this prototype declines.
	 */
	private boolean collectLeaves(PhiInsn phi, BlockNode phiBlock, List<BlockNode> path, InsnArg selector,
			SSAVar stateVar, SwitchInsn sw, BlockNode switchBlock, BlockNode headerBlock,
			Map<InsnNode, BlockNode> insnBlocks, List<Leaf> out, IdentityHashMap<PhiInsn, Boolean> seen,
			@Nullable Integer xorMask) {
		if (seen.put(phi, Boolean.TRUE) != null) {
			return false;
		}
		for (int i = 0; i < phi.getArgsCount(); i++) {
			RegisterArg operand = phi.getArg(i);
			BlockNode pred = phi.getBlockByArgIndex(i);
			if (pred == null || operand.getSVar() == null) {
				return false;
			}
			// See through copies: a conditional next-state (str = cond ? "X" : "Y") lands the diamond's
			// merge phi in a MOVE before the state phi reads it.
			InsnNode def = resolveThroughMoves(operand.getSVar().getAssignInsn());
			// Skip the "state unchanged" self-loop operand: real obfuscated dispatchers split the state
			// into a header phi P_h (the hashCode receiver) and a back-edge merge phi P_m, where the
			// switch's default routes back with P_h unchanged. That P_h-referencing operand of P_m is the
			// trap default (never taken, since every real state matches a concrete case), not a transition.
			if (def == stateVar.getAssignInsn()) {
				continue;
			}
			List<BlockNode> newPath = new ArrayList<>(path);
			newPath.add(pred);
			if (def instanceof ConstStringNode) {
				String value = ((ConstStringNode) def).getString();
				// Fold the selector directly when its constants are known; fall back to the derived XOR
				// mask only when they aren't (an unresolved static field in the chain).
				Integer key = SelectorEval.eval(selector, stateVar, value);
				if (key == null && xorMask != null) {
					key = value.hashCode() ^ xorMask;
				}
				if (key == null) {
					return false;
				}
				BlockNode target = route(sw, key);
				if (target == null || target == switchBlock || target == headerBlock) {
					return false;
				}
				out.add(new Leaf(value, target, newPath, pred, phiBlock, def));
			} else if (def instanceof PhiInsn) {
				// Recurse into the nested next-state phi at ITS OWN block. It need not sit in the immediate
				// predecessor `pred`: javac (and some obfuscators) leave empty pass-through blocks between a
				// ternary's merge phi and the block that feeds the outer phi. Those pass-throughs are on the
				// dead dispatcher path and fall out with it; the leaves' redirect edges come from the nested
				// phi's own operand predecessors, which are the real CFG edges we rewire.
				BlockNode nestedBlock = insnBlocks.get(def);
				if (nestedBlock == null) {
					return false;
				}
				if (!collectLeaves((PhiInsn) def, nestedBlock, newPath, selector, stateVar, sw,
						switchBlock, headerBlock, insnBlocks, out, seen, xorMask)) {
					return false;
				}
			} else {
				return false;
			}
		}
		return true;
	}

	/**
	 * The SSA value of register {@code reg} reaching the end of {@code from} (i.e. what a jump leaving
	 * {@code from} carries). The reaching definition always dominates {@code from}, so we walk the
	 * <b>dominator</b> chain (not predecessors) and return the first block that defines {@code reg} —
	 * an
	 * instruction result, or a phi. Walking dominators is robust to merges that carry {@code reg}
	 * unchanged with no phi (they are just skipped) and to loops (the dominator tree is acyclic).
	 * When the walk reaches the dispatcher header it returns that carried phi's own result
	 * ({@code == rvVar}), which callers read as "value unchanged on this edge" (identity).
	 */
	private static @Nullable RegisterArg reachingValue(int reg, BlockNode from, SSAVar rvVar) {
		for (BlockNode cur = from; cur != null; cur = cur.getIDom()) {
			List<InsnNode> insns = cur.getInstructions();
			for (int i = insns.size() - 1; i >= 0; i--) {
				RegisterArg res = insns.get(i).getResult();
				if (res != null && res.getRegNum() == reg && res.getSVar() != null) {
					return res;
				}
			}
			PhiListAttr pl = cur.get(AType.PHI_LIST);
			if (pl != null) {
				for (PhiInsn phi : pl.getList()) {
					RegisterArg res = phi.getResult();
					if (res != null && res.getRegNum() == reg && res.getSVar() != null) {
						return res;
					}
				}
			}
		}
		return null;
	}

	/** Every target must be reachable from some entry target by following the transition graph. */
	private static boolean allTargetsReachable(Set<BlockNode> entries, Map<BlockNode, List<Leaf>> edgesByTarget,
			Map<Leaf, BlockNode> predTargetOf) {
		Map<BlockNode, List<BlockNode>> succOf = new HashMap<>();
		for (Map.Entry<BlockNode, List<Leaf>> e : edgesByTarget.entrySet()) {
			for (Leaf leaf : e.getValue()) {
				BlockNode pred = predTargetOf.get(leaf);
				if (pred != null) {
					succOf.computeIfAbsent(pred, k -> new ArrayList<>()).add(e.getKey());
				}
			}
		}
		Set<BlockNode> seen = new HashSet<>(entries);
		Deque<BlockNode> work = new ArrayDeque<>(entries);
		while (!work.isEmpty()) {
			for (BlockNode s : succOf.getOrDefault(work.poll(), List.of())) {
				if (seen.add(s)) {
					work.add(s);
				}
			}
		}
		return seen.size() == edgesByTarget.size();
	}

	/**
	 * Feasibility of carried-value resolution: EVERY edge's delivered value must resolve — a concrete
	 * value directly, or (for an "unchanged"/identity edge) the in-value of its predecessor target,
	 * which is itself a merge phi or resolves recursively. Identity chains among single-edge targets
	 * cannot cycle (a cycle passes through a merge target = a loop header, which a phi defines), so
	 * this
	 * terminates. Returning true guarantees {@link #rebuildCarried} can bind every phi operand and
	 * repoint every read without hitting a null.
	 */
	private static boolean resolutionFeasible(Map<BlockNode, List<Leaf>> edgesByTarget,
			Map<Leaf, RegisterArg> delivered, Map<Leaf, BlockNode> predTargetOf, SSAVar rvVar) {
		for (List<Leaf> edges : edgesByTarget.values()) {
			for (Leaf e : edges) {
				if (!operandResolves(e, edgesByTarget, delivered, predTargetOf, rvVar, new HashSet<>())) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * The value {@code e} delivers can be materialised (a concrete value, or a resolvable predecessor).
	 */
	private static boolean operandResolves(Leaf e, Map<BlockNode, List<Leaf>> edgesByTarget,
			Map<Leaf, RegisterArg> delivered, Map<Leaf, BlockNode> predTargetOf, SSAVar rvVar, Set<BlockNode> visiting) {
		RegisterArg v = delivered.get(e);
		if (v == null) {
			return false;
		}
		if (v.getSVar() != rvVar) {
			return true; // concrete value defined in a surviving block
		}
		BlockNode pred = predTargetOf.get(e); // "unchanged": takes the predecessor target's in-value
		return pred != null && inValResolves(pred, edgesByTarget, delivered, predTargetOf, rvVar, visiting);
	}

	/**
	 * The in-value of {@code target} can be materialised (a merge phi, or a resolvable single edge).
	 */
	private static boolean inValResolves(BlockNode target, Map<BlockNode, List<Leaf>> edgesByTarget,
			Map<Leaf, RegisterArg> delivered, Map<Leaf, BlockNode> predTargetOf, SSAVar rvVar, Set<BlockNode> visiting) {
		List<Leaf> edges = edgesByTarget.get(target);
		if (edges == null) {
			return false;
		}
		if (edges.size() >= 2) {
			return true; // a merge phi defines the in-value here
		}
		if (!visiting.add(target)) {
			return false; // single-edge identity cycle — not a shape we can resolve
		}
		return operandResolves(edges.get(0), edgesByTarget, delivered, predTargetOf, rvVar, visiting);
	}

	/** Follow a chain of register {@code MOVE}s to the instruction that actually produces the value. */
	private static @Nullable InsnNode resolveThroughMoves(@Nullable InsnNode def) {
		int guard = 0;
		while (def != null && def.getType() == InsnType.MOVE && guard++ < 64) {
			InsnArg src = def.getArg(0);
			if (!src.isRegister() || ((RegisterArg) src).getSVar() == null) {
				return def;
			}
			def = ((RegisterArg) src).getSVar().getAssignInsn();
		}
		return def;
	}

	/**
	 * The target case block that dominates {@code block} (i.e. which case body it belongs to), or null.
	 */
	private static @Nullable BlockNode classifyTarget(BlockNode block, Set<BlockNode> targets) {
		BlockNode cur = block;
		while (cur != null) {
			if (targets.contains(cur)) {
				return cur;
			}
			cur = cur.getIDom();
		}
		return null;
	}

	/**
	 * Simulate the rewired CFG (each transition's pred -> case block) and return the blocks that become
	 * unreachable.
	 */
	private static Set<BlockNode> deadBlocks(MethodNode mth, List<Leaf> leaves) {
		Map<BlockNode, Map<BlockNode, BlockNode>> rewire = new IdentityHashMap<>();
		for (Leaf leaf : leaves) {
			rewire.computeIfAbsent(leaf.redirectFrom, k -> new IdentityHashMap<>()).put(leaf.redirectOldDest, leaf.target);
		}
		Set<BlockNode> reachable = new HashSet<>();
		Deque<BlockNode> work = new ArrayDeque<>();
		BlockNode enter = mth.getEnterBlock();
		reachable.add(enter);
		work.add(enter);
		while (!work.isEmpty()) {
			BlockNode b = work.poll();
			Map<BlockNode, BlockNode> redir = rewire.get(b);
			for (BlockNode succ : b.getSuccessors()) {
				BlockNode next = redir != null && redir.containsKey(succ) ? redir.get(succ) : succ;
				if (reachable.add(next)) {
					work.add(next);
				}
			}
		}
		Set<BlockNode> dead = new HashSet<>();
		for (BlockNode b : mth.getBasicBlocks()) {
			if (!reachable.contains(b)) {
				dead.add(b);
			}
		}
		return dead;
	}

	/**
	 * Every SSA value defined inside a dead block must be consumed only by dead blocks or by a read we
	 * are about to thread away — otherwise deleting the block would dangle a live reference.
	 */
	private static boolean safeToDelete(Set<BlockNode> dead, Map<InsnNode, BlockNode> insnBlocks, Set<RegisterArg> replacedUses) {
		for (BlockNode b : dead) {
			List<InsnNode> defs = new ArrayList<>(b.getInstructions());
			PhiListAttr pl = b.get(AType.PHI_LIST);
			if (pl != null) {
				defs.addAll(pl.getList());
			}
			for (InsnNode insn : defs) {
				RegisterArg res = insn.getResult();
				SSAVar sv = res == null ? null : res.getSVar();
				if (sv == null) {
					continue;
				}
				for (RegisterArg use : sv.getUseList()) {
					if (replacedUses.contains(use)) {
						continue;
					}
					InsnNode useInsn = use.getParentInsn();
					BlockNode useBlock = useInsn == null ? null : insnBlocks.get(useInsn);
					if (useBlock == null || !dead.contains(useBlock)) {
						return false;
					}
				}
			}
		}
		return true;
	}

	// ---- mutation (only after a plan fully validated) -----------------------------------------------

	private void apply(MethodNode mth, Plan plan) {
		// 1) rewire every transition edge to its target case block. Shared targets (reconvergence / loop
		// headers) simply gain several predecessors.
		for (Leaf leaf : plan.leaves) {
			BlockSplitter.replaceConnection(leaf.redirectFrom, leaf.redirectOldDest, leaf.target);
		}
		// 2) detach the dead dispatcher blocks so every target keeps only its real (rewired) predecessors
		// before we bind merge-phi operands to them (the stale switch->target edges must be gone first).
		for (BlockNode b : plan.dead) {
			b.add(AFlag.REMOVE);
		}
		BlockSplitter.detachMarkedBlocks(mth);
		// 3) rebuild each loop-carried variable: insert merge phis at shared targets and repoint reads.
		for (CarriedVar cv : plan.carried) {
			rebuildCarried(mth, plan, cv);
		}
		// 4) tear down the dispatcher instructions (state phis, back-edge merges, selector, hashCode).
		// Collect every dead instruction and unbind in one batch: unbindInsns removes ALL arg usages
		// first and only then results, so a value defined in one dead block and read in another never
		// trips the "still in use" check.
		List<InsnNode> deadInsns = new ArrayList<>();
		for (BlockNode b : plan.dead) {
			PhiListAttr pl = b.get(AType.PHI_LIST);
			if (pl != null) {
				deadInsns.addAll(pl.getList());
			}
			deadInsns.addAll(b.getInstructions());
		}
		InsnRemover.unbindInsns(mth, deadInsns);
		// 5) drop state-constant assignments left unused in surviving blocks now the state phis are gone
		List<InsnNode> deadConsts = new ArrayList<>();
		for (Leaf leaf : plan.leaves) {
			if (plan.dead.contains(leaf.redirectOldDest)) {
				// const lives in a dead block already unbound above; skip to avoid a double free
			}
			RegisterArg res = leaf.constInsn.getResult();
			SSAVar sv = res == null ? null : res.getSVar();
			if (sv != null && sv.getUseList().isEmpty() && !deadConsts.contains(leaf.constInsn)) {
				deadConsts.add(leaf.constInsn);
			}
		}
		if (!deadConsts.isEmpty()) {
			InsnRemover.removeAllAndUnbind(mth, deadConsts);
		}
		// 6) drop the dead blocks from the method
		BlockProcessor.removeMarkedBlocks(mth);
	}

	/**
	 * Reconstruct one loop-carried variable on the rewired CFG. A merge phi is placed at every
	 * shared-target state; the value entering every other state is resolved by following the recorded
	 * per-edge delivered values (an "unchanged" edge takes its predecessor state's value). Finally
	 * every
	 * read of the old header phi is repointed to the value for the state it belongs to.
	 */
	private void rebuildCarried(MethodNode mth, Plan plan, CarriedVar cv) {
		SSAVar rvVar = cv.rv.getSVar();
		int reg = cv.rv.getRegNum();
		// the carried variable's already-inferred type (type inference does not run again after us)
		ArgType carriedType = rvVar.isCodeVarSet() ? rvVar.getCodeVar().getType() : null;
		if (carriedType == null || !carriedType.isTypeKnown()) {
			carriedType = rvVar.getTypeInfo().getType();
		}
		Map<BlockNode, RegisterArg> inVal = new HashMap<>();
		Map<BlockNode, PhiInsn> phiOf = new LinkedHashMap<>();
		// 1) placeholder merge phis (fresh SSA var) at each merge target
		for (Map.Entry<BlockNode, List<Leaf>> e : plan.edgesByTarget.entrySet()) {
			if (e.getValue().size() < 2) {
				continue;
			}
			BlockNode target = e.getKey();
			PhiInsn phi = SSATransform.addPhi(mth, target, reg);
			RegisterArg res = cv.rv.duplicateWithNewSSAVar(mth);
			if (carriedType != null && carriedType.isTypeKnown()) {
				res.getSVar().setType(carriedType);
			}
			phi.setResult(res);
			phiOf.put(target, phi);
			inVal.put(target, res);
		}
		// 2) resolve the value entering every (single-edge) target
		for (BlockNode target : plan.edgesByTarget.keySet()) {
			resolveInVal(target, plan, cv, rvVar, inVal);
		}
		// 3) bind each merge phi's operands, one per predecessor edge
		for (Map.Entry<BlockNode, PhiInsn> pe : phiOf.entrySet()) {
			PhiInsn phi = pe.getValue();
			for (Leaf leaf : plan.edgesByTarget.get(pe.getKey())) {
				RegisterArg v = cv.delivered.get(leaf);
				RegisterArg operand = (v.getSVar() == rvVar) ? inVal.get(plan.predTargetOf.get(leaf)) : v;
				phi.bindArg(operand.duplicate(), leaf.redirectFrom);
			}
			phi.rebindArgs();
		}
		// 4) repoint every surviving read of the carried variable to the value entering its target
		for (UseSite u : cv.uses) {
			InsnNode useInsn = u.use.getParentInsn();
			if (useInsn != null) {
				useInsn.replaceArg(u.use, inVal.get(u.target).duplicate());
			}
		}
		// 5) collapse any merge phi whose operands are all one value (a carried var unchanged around a
		// loop) into that value, so it does not surface as a spurious variable.
		for (Map.Entry<BlockNode, PhiInsn> pe : phiOf.entrySet()) {
			simplifyPhi(mth, pe.getKey(), pe.getValue());
		}
	}

	/** Value of the carried var entering {@code target}; memoised in {@code inVal}. */
	private static RegisterArg resolveInVal(BlockNode target, Plan plan, CarriedVar cv, SSAVar rvVar,
			Map<BlockNode, RegisterArg> inVal) {
		RegisterArg cached = inVal.get(target);
		if (cached != null) {
			return cached; // merge-target phi result, or already resolved
		}
		Leaf e = plan.edgesByTarget.get(target).get(0); // single edge (merge targets pre-filled above)
		RegisterArg v = cv.delivered.get(e);
		RegisterArg r = (v.getSVar() == rvVar)
				? resolveInVal(plan.predTargetOf.get(e), plan, cv, rvVar, inVal)
				: v;
		inVal.put(target, r);
		return r;
	}

	/** If every operand of {@code phi} is the same SSA var (ignoring self-references), inline it. */
	private static void simplifyPhi(MethodNode mth, BlockNode block, PhiInsn phi) {
		SSAVar phiVar = phi.getResult().getSVar();
		SSAVar unique = null;
		for (int i = 0; i < phi.getArgsCount(); i++) {
			SSAVar a = phi.getArg(i).getSVar();
			if (a == phiVar) {
				continue; // self-reference (unchanged around a loop)
			}
			if (unique == null) {
				unique = a;
			} else if (unique != a) {
				return; // genuinely merges distinct values — keep the phi
			}
		}
		if (unique == null) {
			return;
		}
		RegisterArg replacement = unique.getAssign();
		for (RegisterArg use : new ArrayList<>(phiVar.getUseList())) {
			InsnNode useInsn = use.getParentInsn();
			if (useInsn != null) {
				useInsn.replaceArg(use, replacement.duplicate());
			}
		}
		InsnRemover.unbindInsn(mth, phi);
		PhiListAttr pl = block.get(AType.PHI_LIST);
		if (pl != null) {
			pl.getList().remove(phi);
			if (pl.getList().isEmpty()) {
				block.remove(AType.PHI_LIST);
			}
		}
	}

	// ---- helpers ------------------------------------------------------------------------------------

	/** Map every instruction (including wrapped sub-instructions and phis) to its containing block. */
	private static Map<InsnNode, BlockNode> indexInsnBlocks(MethodNode mth) {
		Map<InsnNode, BlockNode> map = new IdentityHashMap<>();
		for (BlockNode b : mth.getBasicBlocks()) {
			PhiListAttr pl = b.get(AType.PHI_LIST);
			if (pl != null) {
				for (PhiInsn phi : pl.getList()) {
					map.put(phi, b);
				}
			}
			for (InsnNode insn : b.getInstructions()) {
				indexInsn(insn, b, map);
			}
		}
		return map;
	}

	private static void indexInsn(InsnNode insn, BlockNode b, Map<InsnNode, BlockNode> map) {
		map.put(insn, b);
		for (int i = 0; i < insn.getArgsCount(); i++) {
			InsnArg arg = insn.getArg(i);
			if (arg.isInsnWrap()) {
				indexInsn(((InsnWrapArg) arg).getWrapInsn(), b, map);
			}
		}
	}

	private static @Nullable BlockNode route(SwitchInsn sw, int key) {
		int[] keys = sw.getKeys();
		BlockNode[] targets = sw.getTargetBlocks();
		if (keys == null || targets == null || keys.length != targets.length) {
			return null;
		}
		for (int i = 0; i < keys.length; i++) {
			if (keys[i] == key) {
				return targets[i];
			}
		}
		return null;
	}

	/** One resolved state transition. */
	private static final class Leaf {
		final String state;
		final BlockNode target;
		final List<BlockNode> path;
		final BlockNode redirectFrom;
		final BlockNode redirectOldDest;
		final InsnNode constInsn;

		Leaf(String state, BlockNode target, List<BlockNode> path,
				BlockNode redirectFrom, BlockNode redirectOldDest, InsnNode constInsn) {
			this.state = state;
			this.target = target;
			this.path = path;
			this.redirectFrom = redirectFrom;
			this.redirectOldDest = redirectOldDest;
			this.constInsn = constInsn;
		}
	}

	/** A read of a loop-carried variable, tagged with the target case block it belongs to. */
	private static final class UseSite {
		final RegisterArg use;
		final BlockNode target;

		UseSite(RegisterArg use, BlockNode target) {
			this.use = use;
			this.target = target;
		}
	}

	/** Plan for one loop-carried variable: what each edge delivers and which reads to repoint. */
	private static final class CarriedVar {
		final RegisterArg rv; // the old header phi's result (the variable being reconstructed)
		final Map<Leaf, RegisterArg> delivered; // edge -> value at its source (== rv.getSVar() means "unchanged")
		final List<UseSite> uses;

		CarriedVar(RegisterArg rv, Map<Leaf, RegisterArg> delivered, List<UseSite> uses) {
			this.rv = rv;
			this.delivered = delivered;
			this.uses = uses;
		}
	}

	private static final class Plan {
		final List<Leaf> leaves;
		final Set<BlockNode> dead;
		final Map<BlockNode, List<Leaf>> edgesByTarget;
		final Map<Leaf, BlockNode> predTargetOf;
		final List<CarriedVar> carried;

		Plan(List<Leaf> leaves, Set<BlockNode> dead, Map<BlockNode, List<Leaf>> edgesByTarget,
				Map<Leaf, BlockNode> predTargetOf, List<CarriedVar> carried) {
			this.leaves = leaves;
			this.dead = dead;
			this.edgesByTarget = edgesByTarget;
			this.predTargetOf = predTargetOf;
			this.carried = carried;
		}
	}
}
