using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Theory]
    [InlineData(false, false)]
    [InlineData(true, false)]
    [InlineData(false, true)]
    [InlineData(true, true)]
    public void GitCliPairUsesProtectedParentForDemandedChar(bool explicitBase, bool unchanged)
        => CheckAnonymousSource("decide", 0,
            "import Init\nexample : ')' =')' := by decide\n", modified: true,
            prepareContext: true, demandContext: !unchanged, pairBase: explicitBase, unchanged: unchanged);

    [Theory]
    [InlineData("native_decide", 1)]
    [InlineData("decide", 0)]
    public void GitCliAnonymousEmptyReportDispatchesSourceRule(string tactic, int expected)
        => CheckAnonymousSource(tactic, expected);

    [Theory]
    [InlineData(false, false, false)]
    [InlineData(false, true, false)]
    [InlineData(true, false, false)]
    [InlineData(true, true, false)]
    [InlineData(false, false, true)]
    [InlineData(false, true, true)]
    [InlineData(true, false, true)]
    [InlineData(true, true, true)]
    public void GitCliAttributeCharCompilesPreparesAndAdmitsWithEmptyReport(
        bool localTheorem, bool attribute, bool modified)
    {
        var prefix = "import Init\n"
            + (localTheorem ? "theorem attr_control : True := by trivial\n" : "")
            + (attribute ? $"attribute [simp] {(localTheorem ? "attr_control" : "Nat.add_zero")}\n" : "")
            + "example : ')' =')' := by decide\n";
        CheckAnonymousSource("decide", 0, prefix, modified, prepareContext: true);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void GitCliOrdinaryAttributeKeepsDirectNativeDecideRejection(bool genuineChar)
    {
        var prefix = "import Init\nattribute [simp] Nat.add_zero\n"
            + (genuineChar ? "example : True := by native_decide\nexample : ')' =')' := by decide\n" : "");
        CheckAnonymousSource(genuineChar ? "decide" : "native_decide", 1, prefix,
            prepareContext: true, demandContext: false, diagnosticLine: 10);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void GitCliUnmodeledAttributeOnlyRefusesDemandedContext(bool genuineChar, bool native)
    {
        var prefix = "import Lean\nattribute [term_parser] Lean.Parser.Term.paren\n"
            // The certain token precedes the ambiguous Char, so both lexical
            // projections reach it even if one cannot scan the following Char.
            + (genuineChar && native ? "example : True := by native_decide\n" : "")
            + (genuineChar ? "example : ')' =')' := by decide\n" : "");
        var demanded = genuineChar && !native;
        CheckAnonymousSource(native && !genuineChar ? "native_decide" : "decide", genuineChar || native ? 1 : 0,
            prefix, prepareContext: true, demandContext: demanded,
            contextErrorLine: demanded ? 9 : null, diagnosticLine: 10);
    }

    private static void CheckAnonymousSource(string tactic, int expected, string prefix = "",
        bool modified = false, bool prepareContext = false, bool demandContext = true,
        int? contextErrorLine = null, int diagnosticLine = 8, bool? pairBase = null, bool unchanged = false)
    {
        using var temporary = new TemporaryDirectory();
        var root = Path.Combine(temporary.Path, "repository");
        var fixture = TrustedFrozenFixture();
        fixture.Files["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Files["Meta/domains.yaml"] = TestRegistry.Domains;
        foreach (var file in Snapshot(fixture.Files).Entries)
        {
            var target = Path.Combine(root, file.Path);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.WriteAllBytes(target, file.Bytes.ToArray());
        }
        const string path = "D5/S0/Carrier/Anonymous.lean";
        const string header = "/- GID: D5/S0/Carrier/Anonymous\n"
            + "   generality: G\n   mirror-B: none(waiver:test-fixture)\n   mirror-E: none(waiver:test-fixture)\n"
            + "   anchors: []\n   utility: none\n   digest: Anonymous source admission fixture. -/\n";
        if (modified)
            File.WriteAllText(Path.Combine(root, path), header + (unchanged ? prefix : "")
                + "example : True := by decide\n", new UTF8Encoding(false));
        if (prepareContext)
        {
            foreach (var relative in new[] { "lakefile.toml", "lean-toolchain", "lake-manifest.json",
                "tools/lean-inspector/SourceContext.lean", "tools/lean-inspector/SourceOptions.lean",
                "tools/lean-inspector/source-context.py", "tools/lean-inspector/source-context.sh",
                "tools/StrataLint.Cli/Commands/LeanSourceInputCommand.cs",
                "tools/StrataLint.Engine/Ledger/Admission/LeanSourceHeader.cs" })
            {
                var target = Path.Combine(root, relative);
                Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), relative), target, overwrite: true);
            }
            File.WriteAllText(Path.Combine(root, ".gitignore"), ".lake/\n");
        }
        var pair = pairBase.HasValue ? new PairSourcePreparationFixture(temporary.Path, root) : null;
        Git("init", "--quiet");
        Git("add", ".");
        Git("-c", "user.name=Source Context Fixture", "-c", "user.email=source-context@example.invalid",
            "commit", "--quiet", "--no-gpg-sign", "-m", "source fixture baseline");
        var baseline = Git("rev-parse", "HEAD").Trim();
        File.WriteAllText(Path.Combine(root, path), header + prefix + $"example : True := by {tactic}\n", new UTF8Encoding(false));
        Git("add", path);
        if (pair is not null)
        {
            Git("-c", "user.name=Source Context Fixture", "-c", "user.email=source-context@example.invalid",
                "commit", "--quiet", "--no-gpg-sign", "--allow-empty", "-m", "source fixture candidate");
            var candidate = Git("rev-parse", "HEAD").Trim();
            var tree = Git("rev-parse", "HEAD^{tree}").Trim();
            var merge = Git("-c", "user.name=Source Context Fixture", "-c", "user.email=source-context@example.invalid",
                "commit-tree", tree, "-p", baseline, "-p", candidate, "-m", "checked fixture merge").Trim();
            Git("update-ref", "HEAD", merge);
            Assert.Equal(baseline, Git("rev-parse", "HEAD^1").Trim());
        }
        var gateway = new GitRepositoryGateway(root);
        var snapshot = Decode(gateway.ReadCurrent());
        fixture.Reports[path] = new LeanFileReport(prefix.Length == 0 ? [] :
            [prefix.StartsWith("import Lean\n", StringComparison.Ordinal) ? "Lean" : "Init"], []);
        if (pair is not null) fixture.Reports["Trureturing.lean"] = new LeanFileReport(["D5.S0.Carrier.Anonymous"], []);
        const string reportName = "report.json";
        var report = Path.Combine(temporary.Path, reportName);
        RawLeanReportArtifact.WriteFile(report, snapshot, LeanAxiomReport.Create(fixture.Reports));
        Assert.Empty(RawLeanReportArtifact.ReadFile(report, snapshot).Files[RepoPath.CreateKnown(path)].Declarations);
        Assert.False(Directory.Exists(Path.Combine(root, ".lake")));
        byte[]? preparedContext = null;
        if (prepareContext)
        {
            QualifiedSourceContextFixture.EnsureCompilerCache();
            RunPreparation("compile", path);
            Console.WriteLine($"SOURCE_ATTRIBUTE_COMPILE path={path} compile_errors=0 source_sha256="
                + LeanSourceContextInput.SourceHash(snapshot.Files[RepoPath.CreateKnown(path)]));
            if (pair is null) RunPreparation("first");
            else pair.Prepare(report, pairBase == true ? baseline : null, demandContext);
            // Keep the sidecar read visibly rooted in the temporary fixture.
            preparedContext = File.ReadAllBytes(Path.Combine(temporary.Path, reportName + ".source-context.json"));
            if (pair is not null) Directory.Delete(Path.Combine(root, ".lake"), recursive: true);
        }
        // Observe every boundary before the acceptance assertion, including a
        // located producer failure that preparation truthfully publishes at exit 0.
        var input = preparedContext is null ? null : LeanSourceContextInput.Load(preparedContext,
            snapshot, Decode(gateway.ReadRevision(baseline)));
        LeanSourceFileContext? loaded = null;
        var loaderError = input is not null && demandContext ? Record.Exception(() =>
            loaded = input.GetFile(snapshot, RepoPath.CreateKnown(path), "current")) : null;
        var console = new BufferedConsole();
        var code = CliApplication.Run(["check", "--protected-base", baseline, "--candidate-lean-report", report],
            new ProductionCliEnvironment(root, gateway, new FakeLeanReportSource(null)), console);
        Console.WriteLine("SOURCE_ADMISSION_OBSERVATION " + System.Text.Json.JsonSerializer.Serialize(new {
            path, modified, source = snapshot.Files[RepoPath.CreateKnown(path)].Text,
            source_sha256 = LeanSourceContextInput.SourceHash(snapshot.Files[RepoPath.CreateKnown(path)]),
            baseline, report_declarations = 0, producer = preparedContext is null ? null : Encoding.UTF8.GetString(preparedContext),
            loader_error = loaderError?.Message, loader_commands = loaded?.Commands.Length,
            cli_exit = code, cli_stdout = console.Output, cli_stderr = console.Error,
        }));
        Assert.True(code == expected, console.Output + console.Error);
        if (preparedContext is { } bytes)
        {
            using var bundle = System.Text.Json.JsonDocument.Parse(bytes);
            Assert.Equal(demandContext ? 1 : 0, bundle.RootElement.GetProperty("files").GetArrayLength());
            var context = LeanSourceContextInput.Load(bytes,
                snapshot, Decode(gateway.ReadRevision(baseline)));
            if (contextErrorLine is { } errorLine)
            {
                var failure = Assert.Throws<LeanSourceExtractionException>(() =>
                    context.GetFile(snapshot, RepoPath.CreateKnown(path), "current"));
                Assert.Equal(errorLine, failure.Line);
                Assert.Contains("cannot determine this attribute registration effect", failure.Message, StringComparison.Ordinal);
            }
            else if (demandContext)
            {
                Assert.Equal(System.Text.Json.JsonValueKind.Null,
                    bundle.RootElement.GetProperty("files")[0].GetProperty("result").GetProperty("error").ValueKind);
                var parsed = context.GetFile(snapshot, RepoPath.CreateKnown(path), "current");
                Assert.False(parsed.InitialEquality);
                Assert.All(parsed.Commands, command => Assert.False(command.Equality));
            }
            Assert.Empty(context.MalformedRows);
        }
        if (contextErrorLine is { } line)
            Assert.Contains($"NATIVE_DECIDE_CONTEXT_ERROR line={line}", console.Output, StringComparison.Ordinal);
        else if (expected == 1)
            Assert.Contains($"NATIVE_DECIDE_SOURCE line={diagnosticLine}", console.Output, StringComparison.Ordinal);
        else Assert.DoesNotContain("NATIVE_DECIDE_SOURCE", console.Output, StringComparison.Ordinal);
        if (pair is not null && demandContext)
        {
            // Admission must still refuse missing and stale demanded data offline.
            File.Delete(Path.Combine(temporary.Path, reportName + ".source-context.json"));
            AssertContextRejected("missing demanded commands input");
            var stale = System.Text.Json.Nodes.JsonNode.Parse(preparedContext!)!;
            stale["files"]![0]!["sourceSha256"] = new string('0', 64);
            File.WriteAllText(Path.Combine(temporary.Path, reportName + ".source-context.json"), stale.ToJsonString());
            AssertContextRejected("NATIVE_DECIDE_CONTEXT_ERROR");
        }

        void AssertContextRejected(string message)
        {
            var rejected = new BufferedConsole();
            Assert.Equal(1, CliApplication.Run(["check", "--protected-base", baseline, "--candidate-lean-report", report],
                new ProductionCliEnvironment(root, gateway, new FakeLeanReportSource(null)), rejected));
            Assert.Contains(message, rejected.Output, StringComparison.Ordinal);
        }

        void RunPreparation(params string[] arguments)
        {
            var run = TestProcessRunner.Run("python3", ["-c", QualifiedSourceContextScripts.Preparation,
                TestRepositoryLayout.FindRoot(), root, report, baseline, .. arguments], TestRepositoryLayout.FindRoot(),
                BoundedProcessRunner.HangDetectionBudget, 4 * 1024 * 1024);
            Console.WriteLine("SOURCE_PREPARATION_OBSERVATION " + System.Text.Json.JsonSerializer.Serialize(new {
                operation = arguments[0], path, modified,
                source_sha256 = LeanSourceContextInput.SourceHash(snapshot.Files[RepoPath.CreateKnown(path)]),
                exit = run.ExitCode, stdout = Encoding.UTF8.GetString(run.StandardOutput),
                stderr = Encoding.UTF8.GetString(run.StandardError),
            }));
            Assert.True(run.ExitCode == 0, $"{arguments[0]}: " + Encoding.UTF8.GetString(run.StandardOutput)
                + Encoding.UTF8.GetString(run.StandardError));
            Console.WriteLine(Encoding.UTF8.GetString(run.StandardOutput));
        }

        string Git(params string[] arguments)
        {
            var result = TestProcessRunner.Run("git", arguments, root, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
            return Encoding.UTF8.GetString(result.StandardOutput);
        }
    }
}
