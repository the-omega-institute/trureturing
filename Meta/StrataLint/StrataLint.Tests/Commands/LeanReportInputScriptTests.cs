using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanReportInputScriptTests
{
    [Theory]
    [InlineData("source")]
    [InlineData("toolchain")]
    [InlineData("lakefile")]
    [InlineData("manifest")]
    [InlineData("inspector")]
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
                _ => throw new InvalidOperationException($"unknown mutation {mutation}"),
            };
            File.AppendAllText(
                Path.Combine(repository, path),
                "mutation\n",
                new UTF8Encoding(false));
        }

        private ProcessOutput Run(string command) => BoundedProcessRunner.Run(
            "bash",
            [script, command, "--repository", repository, "--report", report],
            temporary.Path,
            TimeSpan.FromSeconds(30),
            1024 * 1024);

        private void Write(string relativePath, string contents) => File.WriteAllText(
            Path.Combine(repository, relativePath.Replace('/', Path.DirectorySeparatorChar)),
            contents,
            new UTF8Encoding(false));

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
}
