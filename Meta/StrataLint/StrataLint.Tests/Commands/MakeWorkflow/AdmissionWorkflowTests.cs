namespace StrataLint.Tests;

public sealed class AdmissionWorkflowTests
{
    [Fact]
    public void ReconcilesStatementProjectionAfterProducingLiveReport()
    {
        var root = FindRepositoryRoot();
        var workflow = File.ReadAllText(Path.Combine(root, ".github", "workflows", "ci.yml"));

        var reportIndex = workflow.IndexOf(
            "name: Produce source-bound canonical Lean reports",
            StringComparison.Ordinal);
        var reconciliationIndex = workflow.IndexOf(
            "name: Reconcile pinned statement projections with live Lean report",
            StringComparison.Ordinal);

        Assert.True(reportIndex >= 0, "admission must produce the canonical live Lean report");
        Assert.True(reconciliationIndex > reportIndex, "reconciliation must run after report production");
        Assert.Contains("STRATALINT_REQUIRE_LIVE_REPORT: \"1\"", workflow, StringComparison.Ordinal);
        Assert.Contains(
            "FullyQualifiedName~LiveReportMatchesPinnedFixtureWhenAvailable",
            workflow,
            StringComparison.Ordinal);
    }

    private static string FindRepositoryRoot()
    {
        for (var directory = new DirectoryInfo(AppContext.BaseDirectory);
             directory is not null;
             directory = directory.Parent)
        {
            if (File.Exists(Path.Combine(directory.FullName, "lakefile.toml")))
                return directory.FullName;
        }

        throw new InvalidOperationException("Repository root was not found.");
    }
}
