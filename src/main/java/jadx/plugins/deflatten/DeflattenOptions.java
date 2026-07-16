package jadx.plugins.deflatten;

import jadx.api.plugins.options.impl.BasePluginOptionsBuilder;

public class DeflattenOptions extends BasePluginOptionsBuilder {

	private boolean enabled = true;
	private boolean comments = true;

	@Override
	public void registerOptions() {
		boolOption(DeflattenPlugin.PLUGIN_ID + ".enabled")
				.description("Undo hashCode-switch control-flow flattening")
				.defaultValue(true)
				.setter(v -> enabled = v);

		boolOption(DeflattenPlugin.PLUGIN_ID + ".comments")
				.description("Add an info comment on each method whose control flow was deflattened")
				.defaultValue(true)
				.setter(v -> comments = v);
	}

	public boolean isEnabled() {
		return enabled;
	}

	public boolean isComments() {
		return comments;
	}
}
