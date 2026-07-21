using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    private const string InspectorSourcePath =
        "Meta/StrataLint/lean-inspector/Inspector.lean";
    private const string InspectorScriptPath =
        "Meta/StrataLint/lean-inspector/inspect.sh";

    [Fact]
    public void PublicMakeTargetEmitsOnlyTheBoundedSnapshotBlock()
    {
        var sourceRoot = FindRepositoryRoot();
        using var temporary = new TemporaryDirectory();
        var repository = Path.Combine(temporary.Path, "repository");
        MaterializeRepositoryInputs(sourceRoot, repository);
        var fakeBin = Path.Combine(temporary.Path, "bin");
        Directory.CreateDirectory(fakeBin);
        var fakeLake = Path.Combine(fakeBin, "lake");
        var fakeDotnet = Path.Combine(fakeBin, "dotnet");
        File.WriteAllText(fakeLake, """
            #!/usr/bin/env bash
            set -euo pipefail
            if [[ "${1:-}" == "env" ]]; then
              while [[ $# -gt 0 ]]; do
                if [[ "$1" == "--output" ]]; then printf '{}\n' > "$2"; exit 0; fi
                shift
              done
              exit 2
            fi
            exit 0
            """ + "\n");
        File.WriteAllText(fakeDotnet, """
            #!/usr/bin/env bash
            set -euo pipefail
            printf '%s\n' '<!-- stratalint:echo-residual-summary:start -->' '# Echo Residual Summary' '' '- candidate_snapshot_sha256: `sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa`' '- baseline_snapshot_sha256: `sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb`' '<!-- stratalint:echo-residual-summary:end -->'
            """ + "\n");
        var executablePaths = new[]
        {
            fakeLake,
            fakeDotnet,
            Path.Combine(repository, InspectorScriptPath),
            Path.Combine(repository, LeanReportPairScriptPath),
            Path.Combine(repository, LeanReportScriptPath),
            Path.Combine(repository, ReportSupervisorScriptPath),
            Path.Combine(repository, LeanReportInputScriptPath),
        };
        var chmod = BoundedProcessRunner.Run(
            "/bin/chmod",
            ["+x", .. executablePaths],
            repository,
            TimeSpan.FromSeconds(10),
            4096);
        Assert.Equal(0, chmod.ExitCode);
        var path = Environment.GetEnvironmentVariable("PATH")
            ?? throw new InvalidOperationException("PATH is required for the Make execution test");

        var result = BoundedProcessRunner.Run(
            "env",
            [
                $"PATH={fakeBin}:{path}",
                $"LAKE_BIN={fakeLake}",
                $"STRATALINT_SUPERVISOR_ROOT={Path.Combine(temporary.Path, "supervisor")}",
                $"STRATALINT_REPORT_METRICS_LOG={Path.Combine(temporary.Path, "metrics.jsonl")}",
                "STRATALINT_LOCK_TIMEOUT_SECONDS=30",
                "make",
                "--no-print-directory",
                "echo-residual-summary",
                "BASE=origin/dev",
            ],
            repository,
            TimeSpan.FromSeconds(60),
            4 * 1024 * 1024);

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.StartsWith(
            "<!-- stratalint:echo-residual-summary:start -->\n",
            output,
            StringComparison.Ordinal);
        Assert.Contains("- candidate_snapshot_sha256: `sha256:", output, StringComparison.Ordinal);
        Assert.Contains("- baseline_snapshot_sha256: `sha256:", output, StringComparison.Ordinal);
        Assert.EndsWith(
            "<!-- stratalint:echo-residual-summary:end -->\n",
            output,
            StringComparison.Ordinal);
        Assert.DoesNotContain("LEAN_REPORT_INPUT", output, StringComparison.Ordinal);
    }

    private static void MaterializeRepositoryInputs(string sourceRoot, string repository)
    {
        var files = new[]
        {
            "Makefile",
            "Trureturing.lean",
            "lake-manifest.json",
            "lakefile.toml",
            "lean-toolchain",
            InspectorSourcePath,
            InspectorScriptPath,
            LeanReportPairScriptPath,
            PerfEventScriptPath,
            EchoResidualSummaryScriptPath,
            LeanReportInputScriptPath,
            LeanReportScriptPath,
            ReportSupervisorScriptPath,
        }.Concat(Directory.GetFiles(
            Path.Combine(sourceRoot, "D5"),
            "*.lean",
            SearchOption.AllDirectories).Select(path => Path.GetRelativePath(sourceRoot, path)));
        foreach (var relativePath in files)
        {
            var destination = Path.Combine(repository, relativePath);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.Copy(Path.Combine(sourceRoot, relativePath), destination);
        }
    }

}
