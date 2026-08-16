using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean report environment")]
public sealed class LeanReportInputScriptTests
{
    private const string InputHelperPath = "tools/scripts/report/lean-report-input.sh";
    private const string RawReportPath = "tools/StrataLint.Engine/Snapshot/RawLeanReportArtifact.cs";
    private const string CanonicalWriterPath = "tools/StrataLint.Engine/Snapshot/StructuredCanonicalWriter.cs";
    private const string LeanModelsPath = "tools/StrataLint.Engine/Snapshot/LeanModels.cs";
    private const string TestSourcePath = "tools/tests/StrataLint.Tests/Snapshot/LeanModelsTests.cs";
    private const string BlueprintSourcePath = "Blueprint/D5/Probe.scribe.cs";
    private static readonly string PairScriptPath = string.Join(
        '/', "tools", "scripts", "lean-report-pair.sh");
    private static readonly string CliProjectPath = string.Join(
        '/', "tools", "StrataLint.Cli", "StrataLint.Cli.csproj");
    private static readonly string EngineProjectPath = string.Join(
        '/', "tools", "StrataLint.Engine", "StrataLint.Engine.csproj");
    private static readonly string EngineLockPath = string.Join(
        '/', "tools", "StrataLint.Engine", "packages.lock.json");
    private static readonly string CliLockPath = string.Join(
        '/', "tools", "StrataLint.Cli", "packages.lock.json");
    private static readonly string ScribeLockPath = string.Join(
        '/', "tools", "StrataLint.Scribe", "packages.lock.json");

    [Fact]
    public void ProductionSourceClosureChangesProducer()
    {
        using var fixture = new LeanReportInputFixture();
        var producerBefore = fixture.Producer();

        fixture.Append(LeanModelsPath, "// mutation\n");

        Assert.NotEqual(producerBefore, fixture.Producer());
    }

    [Fact]
    public void TestProjectSourceDoesNotChangeProducer()
    {
        using var fixture = new LeanReportInputFixture();
        var before = fixture.Producer();

        fixture.Append(TestSourcePath, "// mutation\n");

        Assert.Equal(before, fixture.Producer());
    }

    [Fact]
    public void BlueprintScribeSourceDoesNotChangeProducer()
    {
        using var fixture = new LeanReportInputFixture();
        var before = fixture.Producer();

        fixture.Append(BlueprintSourcePath, "// mutation\n");

        Assert.Equal(before, fixture.Producer());
    }

    [Fact]
    public void DirectoryBuildPropsChangesProducer()
    {
        using var fixture = new LeanReportInputFixture();
        var before = fixture.Producer();

        fixture.Append("Directory.Build.props", "<!-- mutation -->\n");

        Assert.NotEqual(before, fixture.Producer());
    }

    [Fact]
    public void ProducerPathsCommandExposesTheCanonicalDeclaredAndCompileClosure()
    {
        using var fixture = new LeanReportInputFixture();

        var result = fixture.RunCommand("producer-paths");

        Assert.Equal(0, result.ExitCode);
        var paths = Lines(result);
        Assert.Contains(InputHelperPath, paths);
        Assert.Contains("Directory.Build.props", paths);
        Assert.Contains(RawReportPath, paths);
        Assert.Contains(LeanModelsPath, paths);
        Assert.DoesNotContain(TestSourcePath, paths);
        Assert.DoesNotContain(BlueprintSourcePath, paths);
    }

    [Fact]
    public void ModulesEnumerateAllManagedSources()
    {
        using var fixture = new LeanReportInputFixture();
        fixture.WriteSource("D5/Nested/Second.lean", "def second : Nat := 2\n");

        var modules = fixture.RunCommand("modules");

        Assert.Equal(0, modules.ExitCode);
        Assert.Equal(
            new[]
            {
                "Trureturing\tTrureturing.lean",
                "D5.Nested.Second\tD5/Nested/Second.lean",
                "D5.Probe\tD5/Probe.lean",
            },
            Lines(modules));
    }

    [Theory]
    [InlineData("source")]
    [InlineData("toolchain")]
    [InlineData("lakefile")]
    [InlineData("manifest")]
    [InlineData("inspector")]
    [InlineData("inspector-script")]
    [InlineData("input-helper")]
    [InlineData("raw-report")]
    [InlineData("canonical-writer")]
    public void RepositoryInputDriftMakesAnExistingReportStale(string mutation)
    {
        using var fixture = new LeanReportInputFixture();
        Assert.Equal(0, fixture.CaptureProductionInput().ExitCode);
        Assert.Equal(0, fixture.Verify().ExitCode);

        fixture.Mutate(mutation);

        var result = fixture.Verify();
        Assert.Equal(2, result.ExitCode);
        Assert.Contains(
            "stale",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.OrdinalIgnoreCase);
    }

    private sealed class LeanReportInputFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string repository;
        private readonly string report;
        private readonly string script;
        private readonly string inspectorScriptPath = string.Join(
            '/', "tools", "lean-inspector", "inspect.sh");
        private readonly string inspectorSourcePath = string.Join(
            '/', "tools", "lean-inspector", "Inspector.lean");

        internal LeanReportInputFixture()
        {
            repository = Path.Combine(temporary.Path, "repository");
            report = Path.Combine(temporary.Path, "raw-lean-report.json");
            script = Path.Combine(
                TestRepositoryLayout.FindRoot(),
                "tools", "scripts", "report", "lean-report-input.sh");
            Directory.CreateDirectory(Path.Combine(repository, "D5"));
            Directory.CreateDirectory(Path.Combine(
                repository, "tools", "lean-inspector"));
            Write("Trureturing.lean", "import D5.Probe\n");
            Write("D5/Probe.lean", "theorem probe : True := by trivial\n");
            Write("lean-toolchain", "leanprover/lean4:v4.31.0\n");
            Write("lakefile.toml", "name = \"Fixture\"\n");
            Write("lake-manifest.json", "{\"version\":\"1.1.0\"}\n");
            Write(inspectorScriptPath, "#!/usr/bin/env bash\n");
            Write(inspectorSourcePath, "def fixture : True := by trivial\n");
            Write(InputHelperPath, "#!/usr/bin/env bash\n");
            // Cli 工程必须至少有一个编译项:零编译项会让 helper 的 msbuild 求值退化,
            // producer 分量对 Engine 源失敏(阶段 7 删 MergeCommand 桩后实测)。
            Write("tools/StrataLint.Cli/Commands/FixtureProbe.cs", "// fixture\n");
            Write(RawReportPath, "// fixture\n");
            Write(CanonicalWriterPath, "// fixture\n");
            Write(LeanModelsPath, "// fixture\n");
            Write(TestSourcePath, "// fixture\n");
            Write(BlueprintSourcePath, "// fixture\n");
            Write(PairScriptPath, "#!/usr/bin/env bash\n");
            Write("Directory.Build.props", "<Project />\n");
            Write("Directory.Packages.props", "<Project />\n");
            Write(CliProjectPath, "<Project Sdk=\"Microsoft.NET.Sdk\" />\n");
            Write(EngineProjectPath, "<Project Sdk=\"Microsoft.NET.Sdk\" />\n");
            Write(EngineLockPath, "{}\n");
            Write(CliLockPath, "{}\n");
            Write(ScribeLockPath, "{}\n");
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
                _ => throw new InvalidOperationException($"unknown mutation {mutation}"),
            };
            File.AppendAllText(
                Path.Combine(repository, path),
                "mutation\n",
                new UTF8Encoding(false));
        }

        internal ProcessOutput RunCommand(string command) => Run(command);

        internal void WriteSource(string relativePath, string contents) => Write(relativePath, contents);

        internal string Producer()
        {
            var result = Run("address");
            Assert.Equal(0, result.ExitCode);
            return Encoding.UTF8.GetString(result.StandardOutput)
                .Split(' ', StringSplitOptions.RemoveEmptyEntries)[1];
        }

        internal void Append(string relativePath, string contents) => File.AppendAllText(
            Path.Combine(repository, relativePath.Replace('/', Path.DirectorySeparatorChar)),
            contents,
            new UTF8Encoding(false));

        private ProcessOutput Run(string command) => BoundedProcessRunner.Run(
            "bash",
            [script, command, "--repository", repository, "--report", report],
            temporary.Path,
            TimeSpan.FromSeconds(30),
            1024 * 1024);

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
}
