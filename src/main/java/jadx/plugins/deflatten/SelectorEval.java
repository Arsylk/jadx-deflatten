package jadx.plugins.deflatten;

import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Set;

import org.jetbrains.annotations.Nullable;

import jadx.core.dex.instructions.ArithNode;
import jadx.core.dex.instructions.InsnType;
import jadx.core.dex.instructions.InvokeNode;
import jadx.core.dex.instructions.args.InsnArg;
import jadx.core.dex.instructions.args.InsnWrapArg;
import jadx.core.dex.instructions.args.LiteralArg;
import jadx.core.dex.instructions.args.RegisterArg;
import jadx.core.dex.instructions.args.SSAVar;
import jadx.core.dex.nodes.InsnNode;

/**
 * A tiny purpose-built symbolic evaluator for a flattening dispatcher's switch selector.
 *
 * <p>
 * The selector is a pure integer expression rooted at a single {@code String.hashCode()} call on
 * the
 * dispatcher's state variable, folded with compile-time constants (typically an XOR chain, but any
 * integer arithmetic is handled). Given the state variable's SSA var {@code R} and a concrete
 * string
 * value {@code V} that {@code R} can hold, {@link #eval} computes the {@code int} the switch would
 * branch on — i.e. it answers "if {@code str == V}, which case runs?".
 *
 * <p>
 * All arithmetic is performed in {@code int} space so 32-bit overflow (for {@code +}/{@code *}) and
 * the exact {@link String#hashCode()} algorithm match what the app computes at runtime. Any
 * construct
 * outside the recognised pure set (a second hashCode receiver, a field/array read, a non-constant
 * operand, division by zero) yields {@code null}, which callers treat as "not a dispatcher I
 * understand" and leave the method untouched.
 */
final class SelectorEval {

	private static final String STRING_HASHCODE = "java.lang.String.hashCode()I";

	private SelectorEval() {
	}

	/**
	 * Find the single {@code String.hashCode()} receiver the selector {@code arg} depends on.
	 *
	 * @return that receiver's {@link SSAVar}, or {@code null} if there is not exactly one distinct
	 *         receiver (zero, or several — neither is the shape we rewrite)
	 */
	static @Nullable SSAVar findHashCodeReceiver(InsnArg arg) {
		Set<SSAVar> receivers = new HashSet<>();
		collectReceivers(arg, receivers, new IdentityHashMap<>());
		return receivers.size() == 1 ? receivers.iterator().next() : null;
	}

	private static void collectReceivers(@Nullable InsnArg arg, Set<SSAVar> out, IdentityHashMap<InsnNode, Boolean> seen) {
		if (arg == null) {
			return;
		}
		InsnNode insn = producer(arg);
		if (insn == null || seen.put(insn, Boolean.TRUE) != null) {
			return;
		}
		if (isStringHashCode(insn)) {
			InsnArg recv = ((InvokeNode) insn).getInstanceArg();
			if (recv != null && recv.isRegister()) {
				out.add(((RegisterArg) recv).getSVar());
			}
			return; // do NOT recurse into the receiver: it is the loop-carried state var (a phi)
		}
		for (int i = 0; i < insn.getArgsCount(); i++) {
			collectReceivers(insn.getArg(i), out, seen);
		}
	}

	/**
	 * Evaluate the selector for {@code state == value}. Returns the {@code int} switch key, or
	 * {@code null} if the expression contains anything not purely foldable from constants and the
	 * single {@code state.hashCode()}.
	 */
	static @Nullable Integer eval(InsnArg arg, SSAVar state, String value) {
		Long r = evalArg(arg, state, value, new IdentityHashMap<>());
		return r == null ? null : (int) (long) r;
	}

	private static @Nullable Long evalArg(@Nullable InsnArg arg, SSAVar state, String value, IdentityHashMap<InsnNode, Boolean> seen) {
		if (arg == null) {
			return null;
		}
		if (arg.isLiteral()) {
			return ((LiteralArg) arg).getLiteral();
		}
		InsnNode insn = producer(arg);
		if (insn == null) {
			return null;
		}
		return evalInsn(insn, state, value, seen);
	}

	private static @Nullable Long evalInsn(InsnNode insn, SSAVar state, String value, IdentityHashMap<InsnNode, Boolean> seen) {
		if (seen.put(insn, Boolean.TRUE) != null) {
			return null; // cycle in a pure expression -> not foldable
		}
		switch (insn.getType()) {
			case CONST:
				return insn.getArgsCount() == 1 && insn.getArg(0).isLiteral()
						? ((LiteralArg) insn.getArg(0)).getLiteral()
						: null;
			case CAST:
			case MOVE:
				return evalArg(insn.getArg(0), state, value, seen);
			case NEG: {
				Long a = evalArg(insn.getArg(0), state, value, seen);
				return a == null ? null : (long) (-(int) (long) a);
			}
			case NOT: {
				Long a = evalArg(insn.getArg(0), state, value, seen);
				return a == null ? null : (long) (~(int) (long) a);
			}
			case ARITH:
				return evalArith((ArithNode) insn, state, value, seen);
			case INVOKE:
				if (isStringHashCode(insn) && sameState(((InvokeNode) insn).getInstanceArg(), state)) {
					return (long) value.hashCode();
				}
				return null;
			default:
				return null;
		}
	}

	private static @Nullable Long evalArith(ArithNode insn, SSAVar state, String value, IdentityHashMap<InsnNode, Boolean> seen) {
		Long la = evalArg(insn.getArg(0), state, value, seen);
		Long lb = evalArg(insn.getArg(1), state, value, seen);
		if (la == null || lb == null) {
			return null;
		}
		int a = (int) (long) la;
		int b = (int) (long) lb;
		switch (insn.getOp()) {
			case ADD:
				return (long) (a + b);
			case SUB:
				return (long) (a - b);
			case MUL:
				return (long) (a * b);
			case DIV:
				return b == 0 ? null : (long) (a / b);
			case REM:
				return b == 0 ? null : (long) (a % b);
			case AND:
				return (long) (a & b);
			case OR:
				return (long) (a | b);
			case XOR:
				return (long) (a ^ b);
			case SHL:
				return (long) (a << b);
			case SHR:
				return (long) (a >> b);
			case USHR:
				return (long) (a >>> b);
			default:
				return null;
		}
	}

	/** The instruction producing {@code arg}'s value: an inlined wrap, or the assign of a register. */
	private static @Nullable InsnNode producer(InsnArg arg) {
		if (arg.isInsnWrap()) {
			return ((InsnWrapArg) arg).getWrapInsn();
		}
		if (arg.isRegister()) {
			return ((RegisterArg) arg).getAssignInsn();
		}
		return null;
	}

	private static boolean isStringHashCode(InsnNode insn) {
		return insn.getType() == InsnType.INVOKE
				&& STRING_HASHCODE.equals(((InvokeNode) insn).getCallMth().getRawFullId());
	}

	private static boolean sameState(@Nullable InsnArg recv, SSAVar state) {
		return recv != null && recv.isRegister() && ((RegisterArg) recv).getSVar() == state;
	}
}
