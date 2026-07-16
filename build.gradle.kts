plugins {
	java
}

group = "io.github.arsylk"
version = "0.1.0"
description = "jadx plugin: undo hashCode-switch control-flow flattening (CFF deobfuscator)"

repositories {
	mavenCentral()
	google()
}

java {
	sourceCompatibility = JavaVersion.VERSION_11
	targetCompatibility = JavaVersion.VERSION_11
}

dependencies {
	// jadx-core is provided by the host jadx at runtime; never bundle it. This pass drives jadx-core
	// internals (BlockProcessor / BlockSplitter / PhiInsn / SSATransform / InitCodeVariables / …), which
	// ship inside the published jadx-core jar, so the standalone plugin compiles against the pinned Maven
	// artifact like the other fork plugins. Bump together with REQUIRED_JADX_VERSION in DeflattenPlugin.
	compileOnly("io.github.skylot:jadx-core:1.5.2")
	compileOnly("org.slf4j:slf4j-api:2.0.17")
	compileOnly("org.jetbrains:annotations:26.0.2")

	// Tests compile a tiny flattened fixture in-process and decompile it through jadx with this pass
	// enabled (see DeflattenGoldenTest), asserting the deflattened source against a checked-in golden.
	// The released jadx-core + input plugins are pulled from Maven Central so the suite exercises the
	// plugin exactly as it ships standalone (decoupled from the local jadx working tree).
	testImplementation("io.github.skylot:jadx-core:1.5.2")
	testImplementation("io.github.skylot:jadx-java-input:1.5.2")
	testImplementation("org.jetbrains:annotations:26.0.2")
	testImplementation("org.junit.jupiter:junit-jupiter:5.13.3")
	testRuntimeOnly("org.junit.platform:junit-platform-launcher")
	testImplementation("org.assertj:assertj-core:3.27.7")
	testRuntimeOnly("ch.qos.logback:logback-classic:1.5.32")
}

tasks.test {
	useJUnitPlatform()
	outputs.cacheIf { false }
	// `-DupdateGolden=true` regenerates the golden fixtures instead of asserting against them
	systemProperty("updateGolden", System.getProperty("updateGolden", "false"))
	testLogging {
		showStandardStreams = true
		exceptionFormat = org.gradle.api.tasks.testing.logging.TestExceptionFormat.FULL
	}
}

tasks {
	compileJava {
		options.encoding = "UTF-8"
	}
	jar {
		manifest {
			attributes(
				"Implementation-Title" to "jadx-deflatten",
				"Implementation-Version" to project.version,
				"Plugin-Id" to "deflatten",
				"Plugin-Name" to "Control-Flow Deflatten",
			)
		}
	}
}
