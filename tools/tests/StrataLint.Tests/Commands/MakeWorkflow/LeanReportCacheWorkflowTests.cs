namespace StrataLint.Tests;

public sealed class LeanReportCacheWorkflowTests
{
    private const string AdmissionWorkflowPath = ".github/workflows/ci.yml";
    private static readonly string PairScriptPath = string.Join(
        '/', "tools", "scripts", "lean-report-pair.sh");

    [Fact]
    public void ContentAddressedReuseHasNoPrefixFallback()
    {
        var root = TestRepositoryLayout.FindRoot();
        var workflow = File.ReadAllText(Path.Combine(root, AdmissionWorkflowPath));
        var restoreStep = workflow.Split("      - name: Restore canonical Lean report by input address\n", StringSplitOptions.None)[1]
            .Split("      - name: ", StringSplitOptions.None)[0];
        var productionStep = workflow.Split("      - name: Produce source-bound canonical Lean reports\n", StringSplitOptions.None)[1]
            .Split("      - name: ", StringSplitOptions.None)[0];
        var pair = File.ReadAllText(Path.Combine(root, PairScriptPath));

        Assert.DoesNotContain("restore-keys:", restoreStep, StringComparison.Ordinal);
        Assert.DoesNotContain("modules.tsv", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("--module-cache-report", productionStep, StringComparison.Ordinal);
        Assert.DoesNotContain("--module-cache-manifest", productionStep, StringComparison.Ordinal);
        Assert.DoesNotContain("--module-cache-report", pair, StringComparison.Ordinal);
        Assert.DoesNotContain("--module-cache-manifest", pair, StringComparison.Ordinal);
        Assert.DoesNotContain("--modules-file", pair, StringComparison.Ordinal);
    }

}
