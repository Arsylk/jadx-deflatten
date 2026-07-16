package jadx.plugins.deflatten;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
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
 * statically
 * evaluating the selector (see {@link SelectorEval});</li>
 * <li>threads every <i>other</i> loop-carried value (accumulators, cipher handles, ...) that the
 * case
 * bodies read from a header phi: on the linearized path each such read is replaced with the
 * concrete
 * SSA value that phi carried on the edge now leading to that case;</li>
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
		// 1) enumerate state transitions by walking the (possibly nested) state phi tree
		List<Leaf> leaves = new ArrayList<>();
		if (!collectLeaves(statePhi, headerBlock, new ArrayList<>(), selector, stateVar, sw,
				switchBlock, headerBlock, insnBlocks, leaves, new IdentityHashMap<>())) {
			return bail("collectLeaves failed");
		}
		if (leaves.isEmpty()) {
			return bail("no leaves");
		}
		// 2) group transition edges by state and map each state to its (unique) target case block. A
		// state assigned by two different case bodies (reconvergence) or by init + a back-edge (a loop)
		// legitimately has several incoming edges here — that is what earlier versions declined.
		Map<String, List<Leaf>> edgesByState = new LinkedHashMap<>();
		Map<String, BlockNode> targetOf = new LinkedHashMap<>();
		Map<BlockNode, String> targetToState = new LinkedHashMap<>();
		for (Leaf leaf : leaves) {
			edgesByState.computeIfAbsent(leaf.state, k -> new ArrayList<>()).add(leaf);
			BlockNode prevTarget = targetOf.put(leaf.state, leaf.target);
			if (prevTarget != null && prevTarget != leaf.target) {
				return bail("state maps to two targets");
			}
			String prevState = targetToState.put(leaf.target, leaf.state);
			if (prevState != null && !prevState.equals(leaf.state)) {
				return bail("target shared by two states (hashCode collision?)");
			}
		}
		// 3) compute which blocks die once the transitions are rewired
		Set<BlockNode> dead = deadBlocks(mth, leaves);
		if (!dead.contains(switchBlock) || !dead.contains(headerBlock)) {
			return bail("dispatcher core not unreachable after rewire");
		}
		// 4) recover the state graph. The case body assigning a state's constant is its predecessor
		// state; an edge whose constant is not dominated by any case is the entry edge.
		Map<Leaf, String> predStateOf = new IdentityHashMap<>();
		String entryState = null;
		for (Leaf leaf : leaves) {
			BlockNode constBlock = insnBlocks.get(leaf.constInsn);
			if (constBlock == null) {
				return bail("no block for state const");
			}
			String pred = classifyState(constBlock, targetToState);
			predStateOf.put(leaf, pred);
			if (pred == null) {
				if (entryState != null && !entryState.equals(leaf.state)) {
					return bail("two entry states");
				}
				entryState = leaf.state;
			}
		}
		if (entryState == null) {
			return bail("no entry state");
		}
		if (!allStatesReachable(entryState, edgesByState, predStateOf)) {
			return bail("unreachable state in graph");
		}
		// each shared target needs one merge-phi operand per predecessor: the incoming edges must come
		// from distinct, surviving blocks.
		for (List<Leaf> es : edgesByState.values()) {
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
		// and a feasibility check that value resolution — with a merge phi inserted at each shared
		// target — terminates. Nothing is mutated here.
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
				if (!resolutionFeasible(edgesByState, delivered, predStateOf, rvVar)) {
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
					String state = classifyState(useBlock, targetToState);
					if (state == null) {
						return bail("carried read not attributable to a state");
					}
					uses.add(new UseSite(use, state));
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
		for (List<Leaf> es : edgesByState.values()) {
			if (es.size() >= 2) {
				shared++;
			}
		}
		LOG.debug("deflatten: planned {} states ({} shared), {} carried, {} dead in {}",
				edgesByState.size(), shared, carried.size(), dead.size(), mth);
		return new Plan(leaves, dead, edgesByState, targetOf, predStateOf, entryState, carried);
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
			Map<InsnNode, BlockNode> insnBlocks, List<Leaf> out, IdentityHashMap<PhiInsn, Boolean> seen) {
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
				Integer key = SelectorEval.eval(selector, stateVar, value);
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
						switchBlock, headerBlock, insnBlocks, out, seen)) {
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
	 * {@code from} carries). Walks up the single-predecessor chain until it finds a defining
	 * instruction
	 * or a phi for {@code reg}. When it reaches the dispatcher header it returns that carried phi's own
	 * result ({@code == rvVar}), which callers read as "value unchanged on this edge" (identity).
	 */
	private static @Nullable RegisterArg reachingValue(int reg, BlockNode from, SSAVar rvVar) {
		BlockNode cur = from;
		Set<BlockNode> guard = new HashSet<>();
		while (cur != null && guard.add(cur)) {
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
			List<BlockNode> preds = cur.getPredecessors();
			if (preds.size() == 1) {
				cur = preds.get(0);
			} else {
				return null; // a merge without a phi for reg — shouldn't happen for a live carried var
			}
		}
		return null;
	}

	/** Every state must be reachable from the entry by following the transition graph. */
	private static boolean allStatesReachable(String entry, Map<String, List<Leaf>> edgesByState,
			Map<Leaf, String> predStateOf) {
		Map<String, List<String>> succOf = new HashMap<>();
		for (Map.Entry<String, List<Leaf>> e : edgesByState.entrySet()) {
			for (Leaf leaf : e.getValue()) {
				String pred = predStateOf.get(leaf);
				if (pred != null) {
					succOf.computeIfAbsent(pred, k -> new ArrayList<>()).add(e.getKey());
				}
			}
		}
		Set<String> seen = new HashSet<>();
		Deque<String> work = new ArrayDeque<>();
		seen.add(entry);
		work.add(entry);
		while (!work.isEmpty()) {
			for (String s : succOf.getOrDefault(work.poll(), List.of())) {
				if (seen.add(s)) {
					work.add(s);
				}
			}
		}
		return seen.size() == edgesByState.size();
	}

	/**
	 * Feasibility of carried-value resolution: every single-edge state's value must trace (through
	 * "unchanged" identity edges) to either a concrete value or a shared-target state (which will hold
	 * a
	 * merge phi). Single-edge states cannot form a cycle among themselves — a cycle passes through a
	 * shared target (a loop header) — so this always terminates when it returns true.
	 */
	private static boolean resolutionFeasible(Map<String, List<Leaf>> edgesByState,
			Map<Leaf, RegisterArg> delivered, Map<Leaf, String> predStateOf, SSAVar rvVar) {
		for (String s : edgesByState.keySet()) {
			if (!feasible(s, edgesByState, delivered, predStateOf, rvVar, new HashSet<>())) {
				return false;
			}
		}
		return true;
	}

	private static boolean feasible(String s, Map<String, List<Leaf>> edgesByState,
			Map<Leaf, RegisterArg> delivered, Map<Leaf, String> predStateOf, SSAVar rvVar, Set<String> visiting) {
		if (edgesByState.get(s).size() >= 2) {
			return true; // a merge phi will define the value here
		}
		if (!visiting.add(s)) {
			return false; // single-edge cycle — not a shape we can resolve
		}
		Leaf e = edgesByState.get(s).get(0);
		RegisterArg v = delivered.get(e);
		if (v == null) {
			return false;
		}
		if (v.getSVar() == rvVar) { // unchanged: resolves to the predecessor's value
			String pred = predStateOf.get(e);
			return pred != null && feasible(pred, edgesByState, delivered, predStateOf, rvVar, visiting);
		}
		return true;
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
	 * The state whose target case block dominates {@code block} (i.e. which case body it belongs to).
	 */
	private static @Nullable String classifyState(BlockNode block, Map<BlockNode, String> targetToState) {
		BlockNode cur = block;
		while (cur != null) {
			String state = targetToState.get(cur);
			if (state != null) {
				return state;
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
		Map<String, RegisterArg> inVal = new HashMap<>();
		Map<String, PhiInsn> phiOf = new LinkedHashMap<>();
		// 1) placeholder merge phis (fresh SSA var) at each shared-target state
		for (Map.Entry<String, List<Leaf>> e : plan.edgesByState.entrySet()) {
			if (e.getValue().size() < 2) {
				continue;
			}
			BlockNode target = plan.targetOf.get(e.getKey());
			PhiInsn phi = SSATransform.addPhi(mth, target, reg);
			RegisterArg res = cv.rv.duplicateWithNewSSAVar(mth);
			if (carriedType != null && carriedType.isTypeKnown()) {
				res.getSVar().setType(carriedType);
			}
			phi.setResult(res);
			phiOf.put(e.getKey(), phi);
			inVal.put(e.getKey(), res);
		}
		// 2) resolve the value entering every (single-edge) state
		for (String state : plan.edgesByState.keySet()) {
			resolveInVal(state, plan, cv, rvVar, inVal);
		}
		// 3) bind each merge phi's operands, one per predecessor edge
		for (Map.Entry<String, PhiInsn> pe : phiOf.entrySet()) {
			PhiInsn phi = pe.getValue();
			for (Leaf leaf : plan.edgesByState.get(pe.getKey())) {
				RegisterArg v = cv.delivered.get(leaf);
				RegisterArg operand = (v.getSVar() == rvVar) ? inVal.get(plan.predStateOf.get(leaf)) : v;
				phi.bindArg(operand.duplicate(), leaf.redirectFrom);
			}
			phi.rebindArgs();
		}
		// 4) repoint every surviving read of the carried variable to its state's value
		for (UseSite u : cv.uses) {
			InsnNode useInsn = u.use.getParentInsn();
			if (useInsn != null) {
				useInsn.replaceArg(u.use, inVal.get(u.state).duplicate());
			}
		}
		// 5) collapse any merge phi whose operands are all one value (a carried var unchanged around a
		// loop) into that value, so it does not surface as a spurious variable.
		for (Map.Entry<String, PhiInsn> pe : phiOf.entrySet()) {
			simplifyPhi(mth, plan.targetOf.get(pe.getKey()), pe.getValue());
		}
	}

	/** Value of the carried var entering {@code state}; memoised in {@code inVal}. */
	private static RegisterArg resolveInVal(String state, Plan plan, CarriedVar cv, SSAVar rvVar,
			Map<String, RegisterArg> inVal) {
		RegisterArg cached = inVal.get(state);
		if (cached != null) {
			return cached; // shared-target phi result, or already resolved
		}
		Leaf e = plan.edgesByState.get(state).get(0); // single edge (shared targets pre-filled above)
		RegisterArg v = cv.delivered.get(e);
		RegisterArg r = (v.getSVar() == rvVar)
				? resolveInVal(plan.predStateOf.get(e), plan, cv, rvVar, inVal)
				: v;
		inVal.put(state, r);
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

	/** A read of a loop-carried variable, tagged with the state (case body) it belongs to. */
	private static final class UseSite {
		final RegisterArg use;
		final String state;

		UseSite(RegisterArg use, String state) {
			this.use = use;
			this.state = state;
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
		final Map<String, List<Leaf>> edgesByState;
		final Map<String, BlockNode> targetOf;
		final Map<Leaf, String> predStateOf;
		final String entryState;
		final List<CarriedVar> carried;

		Plan(List<Leaf> leaves, Set<BlockNode> dead, Map<String, List<Leaf>> edgesByState,
				Map<String, BlockNode> targetOf, Map<Leaf, String> predStateOf, String entryState,
				List<CarriedVar> carried) {
			this.leaves = leaves;
			this.dead = dead;
			this.edgesByState = edgesByState;
			this.targetOf = targetOf;
			this.predStateOf = predStateOf;
			this.entryState = entryState;
			this.carried = carried;
		}
	}
}
