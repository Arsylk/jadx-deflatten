package jadx.plugins.deflatten;

import jadx.api.plugins.pass.JadxPassInfo;
import jadx.api.plugins.pass.impl.OrderedJadxPassInfo;
import jadx.api.plugins.pass.types.JadxDecompilePass;
import jadx.core.dex.attributes.AFlag;
import jadx.core.dex.instructions.InsnType;
import jadx.core.dex.instructions.InvokeNode;
import jadx.core.dex.instructions.args.InsnArg;
import jadx.core.dex.instructions.args.InsnWrapArg;
import jadx.core.dex.nodes.BlockNode;
import jadx.core.dex.nodes.ClassNode;
import jadx.core.dex.nodes.InsnNode;
import jadx.core.dex.nodes.MethodNode;
import jadx.core.dex.nodes.RootNode;

/**
 * Keeps each method's basic-block graph mutable so {@link DeflattenPass} can rewire CFG edges
 * later.
 *
 * <p>
 * jadx's {@code BlockFinisher} normally locks every block's predecessor/successor lists into
 * immutable collections right after block processing (long before the region maker). {@code
 * DeflattenPass} needs to add and remove edges at the pre-region stage, so this pass runs just
 * before
 * {@code BlockFinisher} and sets {@link AFlag#DISABLE_BLOCKS_LOCK} — the same flag jadx itself uses
 * in
 * its fallback pipeline, so unlocked blocks are a fully supported mode, not a hack.
 */
public class DeflattenUnlockPass implements JadxDecompilePass {

	private final DeflattenOptions options;

	public DeflattenUnlockPass(DeflattenOptions options) {
		this.options = options;
	}

	@Override
	public JadxPassInfo getInfo() {
		return new OrderedJadxPassInfo("DeflattenUnlock", "Keep basic blocks mutable for control-flow deflattening")
				.after("BlockProcessor")
				.before("BlockFinisher");
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
		// Scope the unlock to methods that could actually be a hashCode dispatcher (a SWITCH plus a
		// String.hashCode() call). Everything else keeps jadx's default locked, immutable CFG, so the
		// plugin has no effect on ordinary code even when enabled by default.
		if (options.isEnabled() && !mth.isNoCode() && hasHashCodeSwitch(mth)) {
			mth.add(AFlag.DISABLE_BLOCKS_LOCK);
		}
	}

	private static boolean hasHashCodeSwitch(MethodNode mth) {
		boolean hasSwitch = false;
		boolean hasStringHashCode = false;
		for (BlockNode block : mth.getBasicBlocks()) {
			for (InsnNode insn : block.getInstructions()) {
				if (insn.getType() == InsnType.SWITCH) {
					hasSwitch = true;
				}
				if (containsStringHashCode(insn)) {
					hasStringHashCode = true;
				}
				if (hasSwitch && hasStringHashCode) {
					return true;
				}
			}
		}
		return false;
	}

	private static boolean containsStringHashCode(InsnNode insn) {
		if (insn.getType() == InsnType.INVOKE
				&& "java.lang.String.hashCode()I".equals(((InvokeNode) insn).getCallMth().getRawFullId())) {
			return true;
		}
		for (int i = 0; i < insn.getArgsCount(); i++) {
			InsnArg arg = insn.getArg(i);
			if (arg.isInsnWrap() && containsStringHashCode(((InsnWrapArg) arg).getWrapInsn())) {
				return true;
			}
		}
		return false;
	}
}
