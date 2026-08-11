using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanReportCacheWorkflowTests
{
    private const string AdmissionWorkflowPath = ".github/workflows/ci.yml";

    [Fact]
    public void PerModuleManifestFailureDisablesOnlyTheCacheOptimization()
    {
        var workflow = File.ReadAllText(Path.Combine(FindRepositoryRoot(), AdmissionWorkflowPath));
        var step = workflow.Split("      - name: Reconcile pinned statement projections with live Lean report\n", StringSplitOptions.None)[1]
            .Split("      - name: ", StringSplitOptions.None)[0];

        Assert.Contains("if ! \"$GITHUB_WORKSPACE/baseline/Meta/StrataLint/scripts/report/lean-report-input.sh\" manifest", step, StringComparison.Ordinal);
        Assert.Contains("rm -f -- \"${manifest}.tmp\" \"$manifest\"", step, StringComparison.Ordinal);
        Assert.Contains("full report remains authoritative", step, StringComparison.Ordinal);
    }

    [Fact]
    public void LegacyBaselineInputHelperFallsBackToFullProduction()
    {
        using var temporary = new TemporaryDirectory();
        var workspace = temporary.Path;
        var baselineScripts = Path.Combine(workspace, "baseline", "Meta", "StrataLint", "scripts", "report");
        Directory.CreateDirectory(baselineScripts);
        Directory.CreateDirectory(Path.Combine(workspace, "candidate"));
        var helper = Path.Combine(baselineScripts, "lean-report-input.sh");
        File.WriteAllText(helper, """
            #!/usr/bin/env bash
            set -euo pipefail
            [[ "$1" == "address" && "$2" == "--repository" && "$#" == "3" ]] || exit 2
            printf '%064d %064d x x\n' 1 2
            """);
        Assert.Equal(0, BoundedProcessRunner.Run(
            "chmod", ["+x", helper], workspace, TimeSpan.FromSeconds(30), 4096).ExitCode);

        var workflow = File.ReadAllText(Path.Combine(FindRepositoryRoot(), AdmissionWorkflowPath));
        var step = workflow.Split("      - name: Resolve candidate canonical Lean report address\n", StringSplitOptions.None)[1]
            .Split("      - name: ", StringSplitOptions.None)[0];
        var script = string.Join('\n', step.Split('\n')
            .SkipWhile(line => !line.StartsWith("          set -euo pipefail", StringComparison.Ordinal))
            .TakeWhile(line => line.Length == 0 || line.StartsWith("          ", StringComparison.Ordinal))
            .Select(line => line.Length >= 10 ? line[10..] : line));
        var output = Path.Combine(temporary.Path, "github-output");
        var summary = Path.Combine(temporary.Path, "github-summary");
        var scriptPath = Path.Combine(temporary.Path, "step.sh");
        File.WriteAllText(scriptPath, script);

        var result = BoundedProcessRunner.Run(
            "env",
            [$"GITHUB_WORKSPACE={workspace}", $"GITHUB_OUTPUT={output}", $"GITHUB_STEP_SUMMARY={summary}", "bash", scriptPath],
            workspace,
            TimeSpan.FromSeconds(30),
            16_384);

        Assert.True(result.ExitCode == 0, System.Text.Encoding.UTF8.GetString(result.StandardError));
        var outputs = File.ReadAllText(output);
        Assert.Contains("per-module-compatible=false", outputs, StringComparison.Ordinal);
        Assert.Contains("producer-consistent=false", outputs, StringComparison.Ordinal);
    }

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
