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
