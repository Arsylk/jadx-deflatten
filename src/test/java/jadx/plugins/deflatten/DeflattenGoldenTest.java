package jadx.plugins.deflatten;

import java.io.File;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;

import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;

import org.junit.jupiter.api.Test;

import jadx.api.JadxArgs;
import jadx.api.JadxDecompiler;
import jadx.api.JavaClass;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * End-to-end tests of {@link DeflattenPass}: minimal methods flattened into the
 * {@code while(true) switch(str.hashCode() ^ K)} dispatcher shape are compiled in-process,
 * decompiled
 * through jadx with the plugin enabled, and asserted to come out as ordinary linear control flow.
 *
 * <p>
 * Each fixture mirrors the real Enigma helper: a {@code String} state variable advanced by constant
 * reassignment, with the case keys precomputed as {@code "X".hashCode() ^ K}. The second fixture
 * also
 * exercises <b>loop-carried values</b> (the {@code a}/{@code b} accumulators, analogous to Enigma's
 * {@code cipher}/{@code secretKeySpec} handles) that later states read from earlier ones — the part
 * the pass must thread along the linearized path.
 */
class DeflattenGoldenTest {

	// s = "A" -> +10 -> s = "B" -> +20 -> s = "C" -> return acc ==> 30
	// keys: 'A'=65 ^123 = 58, 'B'=66 ^123 = 57, 'C'=67 ^123 = 56
	private static final String SIMPLE = ""
			+ "public class Flattened {\n"
			+ "    public static int compute() {\n"
			+ "        String s = \"A\";\n"
			+ "        int acc = 0;\n"
			+ "        while (true) {\n"
			+ "            switch (s.hashCode() ^ 123) {\n"
			+ "                case 58: acc += 10; s = \"B\"; break;\n"
			+ "                case 57: acc += 20; s = \"C\"; break;\n"
			+ "                case 56: return acc;\n"
			+ "                default: return -1;\n"
			+ "            }\n"
			+ "        }\n"
			+ "    }\n"
			+ "}\n";

	// two cross-dependent carried ints: a=1,b=2 -> a=a+5(6) -> b=a*b(12) -> return a+b (18)
	// keys: 'A'=65 ^9 = 72, 'B'=66 ^9 = 75, 'C'=67 ^9 = 74
	private static final String CARRIED = ""
			+ "public class Carried {\n"
			+ "    public static int calc() {\n"
			+ "        int a = 1, b = 2;\n"
			+ "        String s = \"A\";\n"
			+ "        while (true) {\n"
			+ "            switch (s.hashCode() ^ 9) {\n"
			+ "                case 72: a = a + 5; s = \"B\"; break;\n"
			+ "                case 75: b = a * b; s = \"C\"; break;\n"
			+ "                case 74: return a + b;\n"
			+ "                default: return -1;\n"
			+ "            }\n"
			+ "        }\n"
			+ "    }\n"
			+ "}\n";

	// no `default:` case, so an unmatched selector falls through and re-loops with the state UNCHANGED.
	// javac compiles that self-loop into the real obfuscator's two-phi shape: a header phi merges the
	// entry value with a back-edge merge phi, whose "state unchanged" operand points back at the header
	// phi itself (the trap default). Exercises collectLeaves' self-loop skip + the relaxed use gate.
	// keys: 'A'=65 ^123 = 58, 'B'=66 ^123 = 57
	private static final String SELFLOOP = ""
			+ "public class SelfLoop {\n"
			+ "    public static int compute() {\n"
			+ "        String s = \"A\";\n"
			+ "        int acc = 0;\n"
			+ "        while (true) {\n"
			+ "            switch (s.hashCode() ^ 123) {\n"
			+ "                case 58: acc += 10; s = \"B\"; break;\n"
			+ "                case 57: return acc;\n"
			+ "            }\n"
			+ "        }\n"
			+ "    }\n"
			+ "}\n";

	@Test
	void deflattensSelfLoopDefault() throws IOException {
		String code = compileAndDecompile(SELFLOOP, "SelfLoop");
		assertDeflattened(code);
		assertMatchesGolden("SelfLoop.java", code);
	}

	@Test
	void deflattensSimpleDispatcher() throws IOException {
		String code = compileAndDecompile(SIMPLE, "Flattened");
		assertDeflattened(code);
		assertMatchesGolden("Flattened.java", code);
	}

	@Test
	void deflattensCarriedValues() throws IOException {
		String code = compileAndDecompile(CARRIED, "Carried");
		assertDeflattened(code);
		assertMatchesGolden("Carried.java", code);
	}

	// conditional transition: state A branches to B or C on `flag`; both are terminal (no reconverge).
	// acc=1, then flag ? return 1+10 : return 1+20 ==> 11 / 21
	// keys: 'A'=65 ^5 = 68, 'B'=66 ^5 = 71, 'C'=67 ^5 = 70
	private static final String COND = ""
			+ "public class Cond {\n"
			+ "    public static int compute(boolean flag) {\n"
			+ "        String s = \"A\";\n"
			+ "        int acc = 0;\n"
			+ "        while (true) {\n"
			+ "            switch (s.hashCode() ^ 5) {\n"
			+ "                case 68: acc += 1; s = flag ? \"B\" : \"C\"; break;\n"
			+ "                case 71: return acc + 10;\n"
			+ "                case 70: return acc + 20;\n"
			+ "                default: return -1;\n"
			+ "            }\n"
			+ "        }\n"
			+ "    }\n"
			+ "}\n";

	// nested dispatchers: the outer B-case contains a whole inner dispatcher whose terminal returns.
	// outer A: acc=1 -> B; inner X: p=acc, p+=100 -> Y; inner Y: return p+200 ==> 301
	// outer keys: 'A'=65 ^3 = 66, 'B'=66 ^3 = 65 ; inner keys: 'X'=88 ^4 = 92, 'Y'=89 ^4 = 93
	private static final String NESTED = ""
			+ "public class Nested {\n"
			+ "    public static int run() {\n"
			+ "        String s = \"A\";\n"
			+ "        int acc = 0;\n"
			+ "        while (true) {\n"
			+ "            switch (s.hashCode() ^ 3) {\n"
			+ "                case 66: acc += 1; s = \"B\"; break;\n"
			+ "                case 65:\n"
			+ "                    String t = \"X\";\n"
			+ "                    int p = acc;\n"
			+ "                    while (true) {\n"
			+ "                        switch (t.hashCode() ^ 4) {\n"
			+ "                            case 92: p += 100; t = \"Y\"; break;\n"
			+ "                            case 93: return p + 200;\n"
			+ "                            default: return -1;\n"
			+ "                        }\n"
			+ "                    }\n"
			+ "                default: return -1;\n"
			+ "            }\n"
			+ "        }\n"
			+ "    }\n"
			+ "}\n";

	// reconvergence: states B and C both advance to a common state D (D's string is assigned by two
	// different case bodies). D reads `acc`, which differs on the two arms (11 vs 21) -> needs a merge
	// phi at D. acc=1, flag ? +10 : +20, return ==> 11 / 21
	// keys: 'A'=65, 'B'=66, 'C'=67, 'D'=68 (K=0)
	private static final String MERGE = ""
			+ "public class Merge {\n"
			+ "    public static int compute(boolean flag) {\n"
			+ "        String s = \"A\";\n"
			+ "        int acc = 0;\n"
			+ "        while (true) {\n"
			+ "            switch (s.hashCode() ^ 0) {\n"
			+ "                case 65: acc += 1; s = flag ? \"B\" : \"C\"; break;\n"
			+ "                case 66: acc += 10; s = \"D\"; break;\n"
			+ "                case 67: acc += 20; s = \"D\"; break;\n"
			+ "                case 68: return acc;\n"
			+ "                default: return -1;\n"
			+ "            }\n"
			+ "        }\n"
			+ "    }\n"
			+ "}\n";

	// loop: state B is a loop header reached from the init (A) and from the body (C) -> two edges into
	// B, a back-edge. i and acc are loop-carried and need phis at B. sums 0..n-1.
	// keys: 'A'=65, 'B'=66, 'C'=67, 'D'=68 (K=0)
	private static final String LOOP = ""
			+ "public class Loop {\n"
			+ "    public static int sum(int n) {\n"
			+ "        String s = \"A\";\n"
			+ "        int i = 0;\n"
			+ "        int acc = 0;\n"
			+ "        while (true) {\n"
			+ "            switch (s.hashCode() ^ 0) {\n"
			+ "                case 65: i = 0; acc = 0; s = \"B\"; break;\n"
			+ "                case 66: s = i < n ? \"C\" : \"D\"; break;\n"
			+ "                case 67: acc += i; i += 1; s = \"B\"; break;\n"
			+ "                case 68: return acc;\n"
			+ "                default: return -1;\n"
			+ "            }\n"
			+ "        }\n"
			+ "    }\n"
			+ "}\n";

	// NEXT TARGET (not yet supported): shared-target state graphs — several state transitions ending at
	// one target block. Covers reconvergence (two case bodies assign the same next-state string) and
	// loops (a loop-header state reached from init + back-edge). Both need carried-value phis inserted
	// at the shared target (localized SSA reconstruction). The pass declines these safely today.
	@Test
	void deflattensMergeReconvergence() throws IOException {
		String code = compileAndDecompile(MERGE, "Merge");
		assertDeflattened(code);
		assertMatchesGolden("Merge.java", code);
	}

	@Test
	void deflattensLoop() throws IOException {
		String code = compileAndDecompile(LOOP, "Loop");
		assertDeflattened(code);
		assertMatchesGolden("Loop.java", code);
	}

	@Test
	void deflattensConditionalTransition() throws IOException {
		String code = compileAndDecompile(COND, "Cond");
		assertDeflattened(code);
		// the two-way state branch must survive as real control flow
		assertThat(code).satisfiesAnyOf(
				c -> assertThat(c).contains(" if "),
				c -> assertThat(c).contains("if ("),
				c -> assertThat(c).contains("?"));
		assertMatchesGolden("Cond.java", code);
	}

	@Test
	void deflattensNestedDispatchers() throws IOException {
		String code = compileAndDecompile(NESTED, "Nested");
		assertDeflattened(code); // the fixpoint must remove BOTH dispatchers
		assertMatchesGolden("Nested.java", code);
	}

	// an ordinary int switch — NOT a hashCode dispatcher. The pass must leave it alone (no false
	// positive); its plain control flow must still decompile correctly (and, lacking a String.hashCode
	// switch, it never even gets unlocked by DeflattenUnlockPass).
	private static final String NORMAL = ""
			+ "public class Normal {\n"
			+ "    public static int pick(int x) {\n"
			+ "        switch (x) {\n"
			+ "            case 1: return 10;\n"
			+ "            case 2: return 20;\n"
			+ "            default: return 0;\n"
			+ "        }\n"
			+ "    }\n"
			+ "}\n";

	@Test
	void leavesNormalSwitchUntouched() throws IOException {
		String code = compileAndDecompile(NORMAL, "Normal");
		System.out.println("=== normal (unchanged) ===\n" + code);
		assertThat(code)
				.doesNotContain("Control-flow deflattened")
				.doesNotContain("Code restructure failed")
				.contains("switch")
				.contains("case 2");
	}

	/** The dispatcher machinery must be gone and a plain body must remain. */
	private static void assertDeflattened(String code) {
		System.out.println("=== deflattened ===\n" + code);
		assertThat(code)
				.doesNotContain("switch")
				.doesNotContain("hashCode")
				.doesNotContain("while")
				.contains("return");
	}

	private static String compileAndDecompile(String source, String className) throws IOException {
		File classDir = compileFixture(source, className);
		JadxArgs args = new JadxArgs();
		args.getInputFiles().add(classDir);
		args.setSkipResources(true);
		try (JadxDecompiler jadx = new JadxDecompiler(args)) {
			jadx.registerPlugin(new DeflattenPlugin());
			jadx.load();
			JavaClass cls = jadx.searchJavaClassByOrigFullName(className);
			assertThat(cls).as("class %s not found", className).isNotNull();
			return cls.getCode();
		}
	}

	private static File compileFixture(String source, String className) throws IOException {
		Path base = Paths.get("build/deflatten-fixture", className);
		Path srcDir = Files.createDirectories(base.resolve("src"));
		Path outDir = Files.createDirectories(base.resolve("out"));
		Path src = srcDir.resolve(className + ".java");
		Files.write(src, source.getBytes(StandardCharsets.UTF_8));

		JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
		assertThat(compiler).as("a JDK (not JRE) is required to run this test").isNotNull();
		int rc = compiler.run(null, null, null, "-d", outDir.toString(), src.toString());
		assertThat(rc).as("fixture %s failed to compile", className).isEqualTo(0);
		return outDir.toFile();
	}

	private static boolean updateGolden() {
		return Boolean.parseBoolean(System.getProperty("updateGolden", "false"));
	}

	private static void assertMatchesGolden(String goldenName, String actual) {
		Path golden = Paths.get("src/test/resources/golden", goldenName);
		try {
			if (updateGolden() || !Files.exists(golden)) {
				Files.createDirectories(golden.getParent());
				Files.write(golden, actual.getBytes(StandardCharsets.UTF_8));
				System.out.println("[golden] wrote " + golden.toAbsolutePath());
				return;
			}
			String expected = new String(Files.readAllBytes(golden), StandardCharsets.UTF_8);
			assertThat(normalize(actual))
					.as("decompiled output drifted from golden %s (re-run with -DupdateGolden=true if intended)", goldenName)
					.isEqualTo(normalize(expected));
		} catch (IOException e) {
			throw new UncheckedIOException(e);
		}
	}

	/** Ignore the volatile info comment the pass adds, and trailing whitespace. */
	private static String normalize(String code) {
		return Arrays.stream(code.split("\n"))
				.filter(line -> !line.contains("Control-flow deflattened:"))
				.map(String::stripTrailing)
				.reduce((a, b) -> a + '\n' + b)
				.orElse("");
	}
}
