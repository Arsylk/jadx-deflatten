package jadx.plugins.deflatten;

import jadx.api.plugins.JadxPlugin;
import jadx.api.plugins.JadxPluginContext;
import jadx.api.plugins.JadxPluginInfo;

/**
 * Undoes control-flow flattening of the {@code while(true) switch(str.hashCode() ^ K)} form used by
 * several string-obfuscators (e.g. the Enigma runtime helper seen in the wild), where a method's
 * real control flow is replaced by a dispatcher loop whose state variable is a {@link String} and
 * whose next-state selector is {@code someString.hashCode()} folded with a chain of constants.
 *
 * <p>
 * A single {@link jadx.api.plugins.pass.types.JadxDecompilePass} runs on the block/SSA IR (after
 * {@code ReplaceNewArray}, before {@code RegionMakerVisitor}): it detects a dispatcher, statically
 * evaluates {@code hashCode(V) ^ K} for each constant state string {@code V}, and rewires every
 * state-transition edge directly to the case block that selector routes to. The dispatcher header,
 * its phi, the {@code hashCode} calls and the constant chain then fall out as dead code, leaving
 * the
 * original (unflattened) control-flow graph for the region maker to structure normally.
 *
 * <p>
 * Sound by construction: a dispatcher is only rewritten when <i>every</i> state string resolves to
 * a
 * compile-time constant that routes to a concrete (non-default) switch case; anything else is left
 * untouched, so the pass can only ever remove flattening it fully understands.
 */
public class DeflattenPlugin implements JadxPlugin {

	public static final String PLUGIN_ID = "deflatten";

	// Keep in sync with build.gradle.kts version and the release tag.
	public static final String VERSION = "0.1.0";

	/**
	 * Minimum jadx version this plugin is built/tested against (surfaced via {@link JadxPluginInfo}).
	 */
	public static final String REQUIRED_JADX_VERSION = "1.5.2, r0";

	private static final String HOMEPAGE = "https://github.com/Arsylk/jadx-deflatten";

	private final DeflattenOptions options = new DeflattenOptions();

	@Override
	public JadxPluginInfo getPluginInfo() {
		JadxPluginInfo info = new JadxPluginInfo(PLUGIN_ID, "Control-Flow Deflatten",
				"Undo hashCode-switch control-flow flattening (rebuild the real CFG from the"
						+ " while(true) switch(str.hashCode() ^ K) dispatcher used by string obfuscators)");
		info.setHomepage(HOMEPAGE);
		info.setRequiredJadxVersion(REQUIRED_JADX_VERSION);
		return info;
	}

	@Override
	public void init(JadxPluginContext context) {
		context.registerOptions(options);
		if (!options.isEnabled()) {
			return;
		}
		// Order matters: DeflattenUnlockPass keeps the CFG mutable (runs before BlockFinisher), then
		// DeflattenPass rewires it (runs after ReplaceNewArray, before RegionMakerVisitor).
		context.addPass(new DeflattenUnlockPass(options));
		context.addPass(new DeflattenPass(options));
	}
}
