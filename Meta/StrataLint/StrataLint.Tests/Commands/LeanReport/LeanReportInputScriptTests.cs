using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanReportInputScriptTests
{
    [Fact]
    public void ManifestKeysIncludeTheTransitiveManagedImportClosure()
    {
        using var fixture = new LeanReportInputFixture();
        fixture.WriteSource("D5/Upstream.lean", "def upstream : Nat := 1\n");
        fixture.WriteSource("D5/Probe.lean", "import D5.Upstream\ntheorem probe : True := by trivial\n");
        fixture.WriteSource("Trureturing.lean", "import D5.Probe\n");
        var before = fixture.Manifest();

        fixture.WriteSource("D5/Upstream.lean", "def upstream : Nat := 2\n");
        var after = fixture.Manifest();

        Assert.Equal(before["D5.Upstream"].Path, after["D5.Upstream"].Path);
        Assert.NotEqual(before["D5.Upstream"].Key, after["D5.Upstream"].Key);
        Assert.NotEqual(before["D5.Probe"].Key, after["D5.Probe"].Key);
        Assert.NotEqual(before["Trureturing"].Key, after["Trureturing"].Key);
    }

    [Fact]
    public void ModulesAndManifestUseTheSameCanonicalEnumeration()
    {
        using var fixture = new LeanReportInputFixture();
        fixture.WriteSource("D5/Nested/Second.lean", "def second : Nat := 2\n");

        var modules = fixture.RunCommand("modules");
        var manifest = fixture.RunCommand("manifest");

        Assert.Equal(0, modules.ExitCode);
        Assert.Equal(0, manifest.ExitCode);
        Assert.Equal(
            Lines(modules).Select(static line => line.Split('\t')[0]),
            Lines(manifest).Select(static line => line.Split('\t')[0]));
    }

    [Theory]
    [InlineData("source")]
    [InlineData("toolchain")]
    [InlineData("lakefile")]
    [InlineData("manifest")]
    [InlineData("inspector")]
    [InlineData("input-helper")]
    [InlineData("merge-cli")]
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
            '/', "Meta", "StrataLint", "lean-inspector", "inspect.sh");
        private readonly string inspectorSourcePath = string.Join(
            '/', "Meta", "StrataLint", "lean-inspector", "Inspector.lean");

        internal LeanReportInputFixture()
        {
            repository = Path.Combine(temporary.Path, "repository");
            report = Path.Combine(temporary.Path, "raw-lean-report.json");
            script = Path.Combine(
                FindRepositoryRoot(),
                "Meta", "StrataLint", "scripts", "report", "lean-report-input.sh");
            Directory.CreateDirectory(Path.Combine(repository, "D5"));
            Directory.CreateDirectory(Path.Combine(
                repository, "Meta", "StrataLint", "lean-inspector"));
            Write("Trureturing.lean", "import D5.Probe\n");
            Write("D5/Probe.lean", "theorem probe : True := by trivial\n");
            Write("lean-toolchain", "leanprover/lean4:v4.31.0\n");
            Write("lakefile.toml", "name = \"Fixture\"\n");
            Write("lake-manifest.json", "{\"version\":\"1.1.0\"}\n");
            Write(inspectorScriptPath, "#!/usr/bin/env bash\n");
            Write(inspectorSourcePath, "def fixture : True := by trivial\n");
            Write("Meta/StrataLint/scripts/report/lean-report-input.sh", "#!/usr/bin/env bash\n");
            Write("Meta/StrataLint/StrataLint.Cli/Commands/LeanReportMergeCommand.cs", "// fixture\n");
            Write("Meta/StrataLint/StrataLint.Engine/Snapshot/RawLeanReportArtifact.cs", "// fixture\n");
            Write("Meta/StrataLint/StrataLint.Engine/Snapshot/StructuredCanonicalWriter.cs", "// fixture\n");
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
            var address = Encoding.UTF8.GetString(result.StandardOutput)
                .Split(' ', StringSplitOptions.RemoveEmptyEntries)[0];
            var reportSha = Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(report)));
            File.WriteAllText(
                report + ".input.attestation",
                "schema=stratalint-lean-report-input-attestation-v1\n"
                + $"repository_input_sha256={address}\n"
                + $"producer_sha256={new string('0', 64)}\n"
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
                "input-helper" => "Meta/StrataLint/scripts/report/lean-report-input.sh",
                "merge-cli" => "Meta/StrataLint/StrataLint.Cli/Commands/LeanReportMergeCommand.cs",
                _ => throw new InvalidOperationException($"unknown mutation {mutation}"),
            };
            File.AppendAllText(
                Path.Combine(repository, path),
                "mutation\n",
                new UTF8Encoding(false));
        }

        internal ProcessOutput RunCommand(string command) => Run(command);

        internal Dictionary<string, (string Path, string Key)> Manifest()
        {
            var result = Run("manifest");
            Assert.Equal(0, result.ExitCode);
            return Lines(result).ToDictionary(
                static line => line.Split('\t')[0],
                static line => (line.Split('\t')[1], line.Split('\t')[2]),
                StringComparer.Ordinal);
        }

        internal void WriteSource(string relativePath, string contents) => Write(relativePath, contents);

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

        private static string FindRepositoryRoot()
        {
            for (var current = new DirectoryInfo(AppContext.BaseDirectory);
                 current is not null;
                 current = current.Parent)
            {
                if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
            }

            throw new DirectoryNotFoundException("Could not locate repository root.");
        }
    }

    private static string[] Lines(ProcessOutput output) => Encoding.UTF8.GetString(output.StandardOutput)
        .Split('\n', StringSplitOptions.RemoveEmptyEntries);
}
