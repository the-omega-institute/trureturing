using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean report environment")]
public sealed partial class LeanReportInputScriptTests
{
    private const string InputHelperPath = "tools/scripts/report/lean-report-input.sh";
    private const string RawReportPath = "tools/StrataLint.Engine/Snapshot/RawLeanReportArtifact.cs";
    private const string CanonicalWriterPath = "tools/Trureturing.Truth/StructuredCanonicalWriter.cs";
    private const string LeanModelsPath = "tools/StrataLint.Engine/Snapshot/LeanModels.cs";
    private const string TestSourcePath = "tools/tests/StrataLint.Tests/Snapshot/LeanModelsTests.cs";
    private const string BlueprintSourcePath = "Blueprint/D5/Probe.scribe.cs";
    private const string ScribeSourcePath = "tools/StrataLint.Scribe/Emission/FixtureEmitter.cs";
    private const string ScribeContentChecksPath =
        "tools/scripts/workflow/scribe-content-checks.sh";
    private static readonly string PairScriptPath = string.Join(
        '/', "tools", "scripts", "lean-report-pair.sh");
    private const string SupervisorScriptPath = "tools/scripts/report/report-supervisor.sh";
    private const string CiBaselineScriptPath =
        "tools/scripts/report/lean-report-ci-baseline.sh";
    private const string CacheEnsureScriptPath =
        "tools/scripts/worktree/lean-cache-ensure.sh";
    private const string CachePublishScriptPath =
        "tools/scripts/worktree/lean-cache-publish.sh";
    private const string ResourceObservationLibraryPath =
        "tools/scripts/lib/resource-observation-lib.sh";
    private const string ToolchainInstallerPath = "tools/scripts/workflow/install-lean-toolchain.sh";
    private const string JudgeContentAddressPath =
        "tools/scripts/workflow/judge-content-address.sh";
    private const string WorkflowPath = ".github/workflows/ci.yml";
    private static readonly string CliProjectPath = string.Join(
        '/', "tools", "StrataLint.Cli", "StrataLint.Cli.csproj");
    private static readonly string EngineProjectPath = string.Join(
        '/', "tools", "StrataLint.Engine", "StrataLint.Engine.csproj");
    private static readonly string ScribeProjectPath = string.Join(
        '/', "tools", "StrataLint.Scribe", "StrataLint.Scribe.csproj");
    private static readonly string EngineLockPath = string.Join(
        '/', "tools", "StrataLint.Engine", "packages.lock.json");
    private static readonly string CliLockPath = string.Join(
        '/', "tools", "StrataLint.Cli", "packages.lock.json");
    private static readonly string ScribeLockPath = string.Join(
        '/', "tools", "StrataLint.Scribe", "packages.lock.json");
    private static readonly string DocumentsProjectPath = string.Join(
        '/', "tools", "StrataLint.Scribe.Documents", "StrataLint.Scribe.Documents.csproj");
    private static readonly string DocumentsLockPath = string.Join(
        '/', "tools", "StrataLint.Scribe.Documents", "packages.lock.json");
    private static readonly string TruthProjectPath = string.Join(
        '/', "tools", "Trureturing.Truth", "Trureturing.Truth.csproj");
    private static readonly string TruthLockPath = string.Join(
        '/', "tools", "Trureturing.Truth", "packages.lock.json");

    internal const string CompatibilityPath = "Meta/lean-report.toml";
    internal const string SourcePatterns = "source_patterns = [\"Trureturing.lean\", \"D5/**/*.lean\"]\n";

    internal static void InstallReportConfiguration(string root)
    {
        Directory.CreateDirectory(Path.Combine(root, "Meta"));
        File.WriteAllText(Path.Combine(root, CompatibilityPath), "compatibility_version = 1\n" + SourcePatterns);
    }

    [Theory]
    [InlineData(LeanModelsPath)]
    [InlineData(RawReportPath)]
    [InlineData(CanonicalWriterPath)]
    [InlineData(TestSourcePath)]
    [InlineData(BlueprintSourcePath)]
    [InlineData("Directory.Build.props")]
    [InlineData("Directory.Packages.props")]
    [InlineData("global.json")]
    [InlineData("tools/StrataLint.Engine/packages.lock.json")]
    [InlineData("tools/lean-inspector/Inspector.lean")]
    [InlineData("tools/lean-inspector/inspect.sh")]
    [InlineData(InputHelperPath)]
    [InlineData(CachePublishScriptPath)]
    [InlineData(".github/workflows/ci.yml")]
    public void FixedVersionImplementationEditsPreserveAddressAndVerification(string path)
    {
        using var fixture = new LeanReportInputFixture();
        Assert.Equal(0, fixture.CaptureProductionInput().ExitCode);
        var before = fixture.Address();

        fixture.Append(path, path.EndsWith(".props", StringComparison.Ordinal)
            ? "\n<!-- implementation changed -->\n" : "\n ");

        Assert.Equal(before, fixture.Address());
        Assert.Equal(0, fixture.Verify().ExitCode);
    }

    [Fact]
    public void CompatibilityVersionBumpChangesTokenAndRejectsOldReport()
    {
        using var fixture = new LeanReportInputFixture();
        Assert.Equal(0, fixture.CaptureProductionInput().ExitCode);
        var before = fixture.RunCommand("address");
        fixture.WriteSource(CompatibilityPath, "compatibility_version = 2\n" + SourcePatterns);

        var after = fixture.RunCommand("address");

        Assert.Equal(0, after.ExitCode);
        Assert.NotEqual(Fields(before)[0], Fields(after)[0]);
        Assert.NotEqual(Fields(before)[1], Fields(after)[1]);
        Assert.Equal(Fields(before)[2..], Fields(after)[2..]);
        Assert.Equal(2, fixture.Verify().ExitCode);
    }

    [Theory]
    [InlineData(null)]
    [InlineData("")]
    [InlineData("compatibility_version = 0\n")]
    [InlineData("compatibility_version = -1\n")]
    [InlineData("compatibility_version = true\n")]
    [InlineData("compatibility_version = \"1\"\n")]
    [InlineData("compatibility_version = 1.0\n")]
    [InlineData("compatibility_version = 01\n")]
    [InlineData("compatibility_version = 1\ncompatibility_version = 2\n")]
    [InlineData("compatibility_version = 1\nunknown = 2\n")]
    public void InvalidCompatibilityVersionFailsSpecifically(string? version)
    {
        using var fixture = new LeanReportInputFixture();
        Assert.Equal(0, fixture.CaptureProductionInput().ExitCode);
        if (version is null) fixture.RemoveSource(CompatibilityPath);
        else fixture.WriteSource(CompatibilityPath, version + SourcePatterns);

        foreach (var command in new[] { "address", "verify", "modules", "compatibility-token" })
        {
            var result = fixture.RunCommand(command);
            Assert.Equal(2, result.ExitCode);
            Assert.Empty(result.StandardOutput);
            Assert.Contains("compatibility_version", Encoding.UTF8.GetString(result.StandardError));
            Assert.Contains(CompatibilityPath, Encoding.UTF8.GetString(result.StandardError));
        }
    }

    [Fact]
    public void ManifestFormattingDoesNotChangeCompatibilityOrAddress()
    {
        using var fixture = new LeanReportInputFixture();
        var before = fixture.Address();
        fixture.WriteSource(CompatibilityPath,
            "# developer comment\n  compatibility_version = 1  # unchanged\n\n" + SourcePatterns);
        Assert.Equal(before, fixture.Address());
    }

    [Fact]
    public void ScribeSelectionDoesNotChangeReportIdentity()
    {
        using var fixture = new LeanReportInputFixture();
        var before = fixture.Address();
        fixture.Append(CompatibilityPath, "scribe_check_inputs = [\"tools/Explicit/*.cs\"]\n");
        Assert.Equal(before, fixture.Address());
    }

    [Theory]
    [InlineData("")]
    [InlineData("source_patterns = [\"../outside.lean\"]\n")]
    [InlineData("source_patterns = [\"Trureturing.lean\", \"D5/**/*.lean\", \"D5/Probe.lean\"]\n")]
    public void MissingOrConflictingSourceRegistrationFailsWithoutFallback(string sources)
    {
        using var fixture = new LeanReportInputFixture();
        fixture.WriteSource(CompatibilityPath, "compatibility_version = 1\n" + sources);
        var result = fixture.RunCommand("address");
        Assert.Equal(2, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        Assert.Contains("source_patterns", Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void VerifyRejectsAttestedProducerThatDiffersFromCurrentProducer()
    {
        using var fixture = new LeanReportInputFixture();
        Assert.Equal(0, fixture.CaptureProductionInput().ExitCode);
        fixture.RewriteAttestedProducer(new string('0', 64));
        var result = fixture.Verify();
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("producer", Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void ModulesAndReportSourcesUseTheSameRegisteredSelection()
    {
        using var fixture = new LeanReportInputFixture();
        fixture.WriteSource("D5/Nested/Second.lean", "def second : Nat := 2\n");
        fixture.WriteSource("tools/lean-inspector/Unused/Probe.lean", "-- unused fixture\n");
        Assert.Equal(new[] { "Trureturing\tTrureturing.lean", "D5.Nested.Second\tD5/Nested/Second.lean", "D5.Probe\tD5/Probe.lean" },
            Lines(fixture.RunCommand("modules")));
        Assert.Equal(fixture.ManifestHash("Trureturing.lean", "D5/Nested/Second.lean", "D5/Probe.lean"),
            fixture.CacheIdentity().Sources);
    }

    [Fact]
    public void CacheClosureHashesSeparateConfigurationFromSources()
    {
        using var fixture = new LeanReportInputFixture();
        if (!OperatingSystem.IsWindows()) fixture.InitializeGitRepository();
        var before = fixture.CacheIdentity();
        fixture.AssertMemoBehavior(before);
        fixture.Append("lean-toolchain", "mutation\n");
        var configChanged = fixture.CacheIdentity();
        Assert.NotEqual(before.Config, configChanged.Config);
        Assert.Equal(before.Sources, configChanged.Sources);
        fixture.Append("D5/Probe.lean", "mutation\n");
        var sourceChanged = fixture.CacheIdentity();
        Assert.Equal(configChanged.Config, sourceChanged.Config);
        Assert.NotEqual(configChanged.Sources, sourceChanged.Sources);
    }

    [Theory]
    [InlineData("repository")]
    [InlineData("repository[cache]")]
    public void InspectorSourcesOnlyInvalidateCompiledCache(string repositoryName)
    {
        using var fixture = new LeanReportInputFixture(repositoryName);
        var reportBefore = fixture.RunCommand("address");
        var cacheBefore = fixture.CompiledCacheAddress();
        fixture.WriteSource("tools/lean-inspector/Unused/Probe.lean", "-- added unused fixture\n");
        Assert.Equal(reportBefore.StandardOutput, fixture.RunCommand("address").StandardOutput);
        var cacheAfter = fixture.CompiledCacheAddress();
        Assert.NotEqual(Fields(cacheBefore)[0], Fields(cacheAfter)[0]);
        Assert.Equal(Fields(cacheBefore)[1], Fields(cacheAfter)[1]);
        Assert.Equal(fixture.CacheIdentity().Config, Fields(cacheAfter)[1].Trim());
    }

    [Fact]
    public void SourceAdditionsChangesAndDeletionsInvalidateReport()
    {
        using var fixture = new LeanReportInputFixture();
        var before = fixture.CacheIdentity();
        fixture.Append("D5/Probe.lean", " ");
        Assert.NotEqual(before.Sources, fixture.CacheIdentity().Sources);
        fixture.WriteSource("D5/Probe.lean", "theorem probe : True := by trivial\n");
        Assert.Equal(before, fixture.CacheIdentity());
        fixture.WriteSource("D5/Copy.lean", "theorem probe : True := by trivial\n");
        Assert.NotEqual(before.Sources, fixture.CacheIdentity().Sources);
        fixture.RemoveSource("D5/Copy.lean");
        Assert.Equal(before, fixture.CacheIdentity());
    }

    [Theory]
    [InlineData("source")]
    [InlineData("toolchain")]
    [InlineData("lakefile")]
    [InlineData("manifest")]
    public void RepositoryInputDriftMakesAnExistingReportStale(string mutation)
    {
        using var fixture = new LeanReportInputFixture();
        Assert.Equal(0, fixture.CaptureProductionInput().ExitCode);
        Assert.Equal(0, fixture.Verify().ExitCode);
        fixture.Mutate(mutation);
        var result = fixture.Verify();
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("stale", Encoding.UTF8.GetString(result.StandardError), StringComparison.OrdinalIgnoreCase);
    }

    private sealed partial class LeanReportInputFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string repository;
        private readonly string report;
        private readonly string script;
        private readonly string inspectorScriptPath = string.Join(
            '/', "tools", "lean-inspector", "inspect.sh");
        private readonly string inspectorSourcePath = string.Join(
            '/', "tools", "lean-inspector", "Inspector.lean");

        internal LeanReportInputFixture(string repositoryName = "repository")
        {
            repository = Path.Combine(temporary.Path, repositoryName);
            report = Path.Combine(temporary.Path, "raw-lean-report.json");
            script = Path.Combine(
                TestRepositoryLayout.FindRoot(),
                "tools", "scripts", "report", "lean-report-input.sh");
            Directory.CreateDirectory(Path.Combine(repository, "D5"));
            Directory.CreateDirectory(Path.Combine(
                repository, "tools", "lean-inspector"));
            InstallReportConfiguration(repository);
            Write("Trureturing.lean", "import D5.Probe\n");
            Write("D5/Probe.lean", "theorem probe : True := by trivial\n");
            Write("lean-toolchain", "leanprover/lean4:v4.31.0\n");
            Write("lakefile.toml", "name = \"Fixture\"\n");
            Write("lake-manifest.json", "{\"version\":\"1.1.0\"}\n");
            Write(inspectorScriptPath, "#!/usr/bin/env bash\n");
            Write(inspectorSourcePath, "def fixture : True := by trivial\n");
            Write(InputHelperPath, "#!/usr/bin/env bash\n");
            Write("tools/scripts/worktree/lean-cache-input.sh", File.ReadAllText(
                Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean-cache-input.sh"),
                Encoding.UTF8));
            Write("tools/StrataLint.Cli/Commands/FixtureProbe.cs", "// fixture\n");
            Write(RawReportPath, "// fixture\n");
            Write(CanonicalWriterPath, "// fixture\n");
            Write(LeanModelsPath, "// fixture\n");
            Write(TestSourcePath, "// fixture\n");
            Write(BlueprintSourcePath, "// fixture\n");
            Write(ScribeSourcePath, "// fixture\n");
            Write(
                PairScriptPath,
                File.ReadAllText(
                    Path.Combine(
                        TestRepositoryLayout.FindRoot(),
                        "tools", "scripts", "lean-report-pair.sh"),
                    Encoding.UTF8));
            Write(
                SupervisorScriptPath,
                File.ReadAllText(
                    Path.Combine(
                        TestRepositoryLayout.FindRoot(),
                        "tools", "scripts", "report", "report-supervisor.sh"),
                    Encoding.UTF8));
            Write(
                CiBaselineScriptPath,
                File.ReadAllText(
                    Path.Combine(
                        TestRepositoryLayout.FindRoot(),
                        "tools", "scripts", "report", "lean-report-ci-baseline.sh"),
                    Encoding.UTF8));
            Write(CacheEnsureScriptPath, "#!/usr/bin/env bash\n");
            Write(
                CachePublishScriptPath,
                File.ReadAllText(
                    Path.Combine(
                        TestRepositoryLayout.FindRoot(),
                        "tools", "scripts", "worktree", "lean-cache-publish.sh"),
                    Encoding.UTF8));
            Write(
                ResourceObservationLibraryPath,
                File.ReadAllText(
                    Path.Combine(
                        TestRepositoryLayout.FindRoot(),
                        "tools", "scripts", "lib", "resource-observation-lib.sh"),
                    Encoding.UTF8));
            Write(ToolchainInstallerPath, "#!/usr/bin/env bash\n");
            Write(
                JudgeContentAddressPath,
                File.ReadAllText(
                    Path.Combine(
                        TestRepositoryLayout.FindRoot(),
                        "tools", "scripts", "workflow", "judge-content-address.sh"),
                    Encoding.UTF8));
            Write(ScribeContentChecksPath, "#!/usr/bin/env bash\n");
            Write(WorkflowPath, "# unrelated CI code fixture\n");
            Write("Directory.Build.props", "<Project />\n");
            Write("Directory.Packages.props", "<Project />\n");
            Write(CliProjectPath, "<Project Sdk=\"Microsoft.NET.Sdk\" />\n");
            Write(EngineProjectPath, "<Project Sdk=\"Microsoft.NET.Sdk\" />\n");
            Write(ScribeProjectPath, "<Project Sdk=\"Microsoft.NET.Sdk\" />\n");
            Write(
                DocumentsProjectPath,
                "<Project Sdk=\"Microsoft.NET.Sdk\"><ItemGroup>"
                    + "<Compile Include=\"../../Blueprint/**/*.scribe.cs\" />"
                    + "</ItemGroup></Project>\n");
            Write(TruthProjectPath, "<Project Sdk=\"Microsoft.NET.Sdk\" />\n");
            Write(EngineLockPath, "{}\n");
            Write(CliLockPath, "{}\n");
            Write(ScribeLockPath, "{}\n");
            Write(DocumentsLockPath, "{}\n");
            Write(TruthLockPath, "{}\n");
            Write("global.json", "{}\n");
            File.WriteAllText(report, "{}\n", new UTF8Encoding(false));
            var digest = Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(report)));
            File.WriteAllText(
                report + ".sha256",
                $"{digest}  {Path.GetFileName(report)}\n",
                new UTF8Encoding(false));
            File.WriteAllText(
                report + ".provenance.json",
                "{}\n",
                new UTF8Encoding(false));
        }

        internal string MemoRoot => Path.Combine(temporary.Path, "memo");

        internal string MemoFile => Path.Combine(MemoRoot, "memo.v1");

        internal ProcessOutput CaptureProductionInput()
        {
            var result = Run("address");
            if (result.ExitCode != 0) return result;
            var addressParts = Encoding.UTF8.GetString(result.StandardOutput)
                .Split(' ', StringSplitOptions.RemoveEmptyEntries);
            var address = addressParts[0];
            var producer = addressParts[1];
            var reportSha = Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(report)));
            File.WriteAllText(
                report + ".input.attestation",
                "schema=stratalint-lean-report-input-attestation-v1\n"
                + $"repository_input_sha256={address}\n"
                + $"producer_sha256={producer}\n"
                + $"report_sha256={reportSha}\n",
                new UTF8Encoding(false));
            return result;
        }

        internal ProcessOutput Verify() => Run("verify");

        internal void RewriteAttestedProducer(string producer)
        {
            var path = report + ".input.attestation";
            var lines = File.ReadAllLines(path, Encoding.UTF8);
            Assert.Equal(4, lines.Length);
            lines[2] = $"producer_sha256={producer}";
            File.WriteAllLines(path, lines, new UTF8Encoding(false));
        }

        internal void Mutate(string mutation)
        {
            var path = mutation switch
            {
                "source" => "D5/Probe.lean",
                "toolchain" => "lean-toolchain",
                "lakefile" => "lakefile.toml",
                "manifest" => "lake-manifest.json",
                "inspector" => inspectorSourcePath,
                "inspector-script" => inspectorScriptPath,
                "input-helper" => InputHelperPath,
                "raw-report" => RawReportPath,
                "canonical-writer" => CanonicalWriterPath,
                "cache-fetcher" => CachePublishScriptPath,
                _ => throw new InvalidOperationException($"unknown mutation {mutation}"),
            };
            File.AppendAllText(
                Path.Combine(repository, path),
                "mutation\n",
                new UTF8Encoding(false));
        }

        internal ProcessOutput RunCommand(string command) => Run(command);

        internal void WriteSource(string relativePath, string contents) => Write(relativePath, contents);

        internal void InitializeGitRepository()
        {
            ReviewRegressionTests.RunGit(repository, "init", "--quiet");
            ReviewRegressionTests.RunGit(repository, "config", "user.email", "stratalint@example.invalid");
            ReviewRegressionTests.RunGit(repository, "config", "user.name", "StrataLint Tests");
            ReviewRegressionTests.RunGit(repository, "add", ".");
            ReviewRegressionTests.RunGit(repository, "commit", "--quiet", "-m", "lean input fixture");
        }

        internal void AssertMemoBehavior((string Sources, string Config) before)
        {
            if (OperatingSystem.IsWindows()) return;

            Assert.True(File.Exists(MemoFile));
            var memo = File.ReadAllBytes(MemoFile);
            Assert.Equal(before, CacheIdentity());

            PoisonSourceMemo();
            File.SetUnixFileMode(
                MemoRoot,
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute
                    | UnixFileMode.GroupRead | UnixFileMode.GroupWrite | UnixFileMode.GroupExecute
                    | UnixFileMode.OtherRead | UnixFileMode.OtherWrite | UnixFileMode.OtherExecute);
            Assert.Equal(before, CacheIdentity());

            File.SetUnixFileMode(
                MemoRoot,
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
            foreach (var failure in new[] { "malformed", "unreadable" })
            {
                File.WriteAllBytes(MemoFile, memo);
                MakeMemoUnusable(failure);
                Assert.Equal(before, CacheIdentity());
                File.SetUnixFileMode(
                    MemoFile,
                    UnixFileMode.UserRead | UnixFileMode.UserWrite);
            }
            File.WriteAllBytes(MemoFile, memo);
        }

        [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
        internal void MakeMemoUnusable(string failure)
        {
            if (failure == "malformed")
            {
                File.WriteAllText(MemoFile, "not a memo\n", new UTF8Encoding(false));
                return;
            }

            Assert.Equal("unreadable", failure);
            File.SetUnixFileMode(MemoFile, 0);
        }

        internal void PoisonSourceMemo()
        {
            var sourceOid = ReviewRegressionTests.RunGit(
                    repository, "rev-parse", "HEAD:D5/Probe.lean")
                .Trim();
            var lines = File.ReadAllLines(MemoFile);
            var index = Array.FindIndex(
                lines,
                line => line.StartsWith(sourceOid + " ", StringComparison.Ordinal));
            Assert.True(index >= 0, "source blob is absent from memo");
            lines[index] = $"{sourceOid} {new string('0', 64)}";
            File.WriteAllLines(MemoFile, lines, new UTF8Encoding(false));
        }

        internal string Producer()
        {
            var result = Run("address");
            Assert.Equal(0, result.ExitCode);
            return Encoding.UTF8.GetString(result.StandardOutput)
                .Split(' ', StringSplitOptions.RemoveEmptyEntries)[1];
        }

        internal string Address()
        {
            var result = Run("address");
            Assert.Equal(0, result.ExitCode);
            return Encoding.UTF8.GetString(result.StandardOutput)
                .Split(' ', StringSplitOptions.RemoveEmptyEntries)[0];
        }

        internal (string Sources, string Config) CacheIdentity()
        {
            var result = Run("address");
            Assert.Equal(0, result.ExitCode);
            var parts = Encoding.UTF8.GetString(result.StandardOutput)
                .Split(' ', StringSplitOptions.RemoveEmptyEntries);
            Assert.Equal(4, parts.Length);
            return (parts[2], parts[3].Trim());
        }

        internal void Append(string relativePath, string contents) => File.AppendAllText(
            Path.Combine(repository, relativePath.Replace('/', Path.DirectorySeparatorChar)),
            contents,
            new UTF8Encoding(false));

        internal void RemoveInspectorDirectory() => Directory.Delete(
            Path.Combine(repository, "tools", "lean-inspector"),
            recursive: true);

        internal string ManifestHash(params string[] relativePaths)
        {
            var manifest = new StringBuilder();
            foreach (var relativePath in relativePaths)
            {
                var path = Path.Combine(
                    repository,
                    relativePath.Replace('/', Path.DirectorySeparatorChar));
                var digest = Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(path)));
                manifest.Append(digest).Append("  ").Append(relativePath).Append('\n');
            }
            return Convert.ToHexStringLower(
                SHA256.HashData(Encoding.UTF8.GetBytes(manifest.ToString())));
        }

        private ProcessOutput Run(string command, string? workingDirectory = null)
        {
            var arguments = new List<string>
            {
                $"STRATALINT_LEAN_INPUT_MEMO_ROOT={MemoRoot}",
            };
            arguments.AddRange(
            [
                "bash", script, command, "--repository", repository, "--report", report,
            ]);
            return TestProcessRunner.Run(
                "env",
                arguments,
                workingDirectory ?? temporary.Path,
                BoundedProcessRunner.HangDetectionBudget,
                1024 * 1024);
        }

        private void Write(string relativePath, string contents)
        {
            var path = Path.Combine(repository, relativePath.Replace('/', Path.DirectorySeparatorChar));
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, contents, new UTF8Encoding(false));
        }

        public void Dispose() => temporary.Dispose();

    }

    private static string[] Lines(ProcessOutput output) => Encoding.UTF8.GetString(output.StandardOutput)
        .Split('\n', StringSplitOptions.RemoveEmptyEntries);

    private static string[] Fields(ProcessOutput output) => Encoding.UTF8.GetString(output.StandardOutput)
        .Split(' ', StringSplitOptions.RemoveEmptyEntries);
}
