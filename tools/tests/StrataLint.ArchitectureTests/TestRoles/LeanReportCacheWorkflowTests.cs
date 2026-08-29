using StrataLint.ScriptTests;
using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

public sealed class LeanReportCacheWorkflowTests
{
    [Fact]
    public void ContentAddressedReuseHasNoPrefixFallback()
    {
        var workflow = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            ".github/workflows/ci.yml"));
        var restoreStep = workflow.Split("      - name: Restore canonical Lean report by input address\n", StringSplitOptions.None)[1]
            .Split("      - name: ", StringSplitOptions.None)[0];
        var productionStep = workflow.Split("      - name: Produce source-bound canonical Lean reports\n", StringSplitOptions.None)[1]
            .Split("      - name: ", StringSplitOptions.None)[0];
        var reuseStep = workflow.Split(
                "      - name: Serve candidate canonical Lean report from the cached address\n",
                StringSplitOptions.None)[1]
            .Split("      - name: ", StringSplitOptions.None)[0];
        var stagingStep = workflow.Split(
                "      - name: Stage candidate canonical Lean report cache\n",
                StringSplitOptions.None)[1]
            .Split("      - name: ", StringSplitOptions.None)[0];
        var pair = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools/scripts/lean-report-pair.sh"));

        Assert.Contains("restore-keys: stratalint-canonical-lean-report-v2-", restoreStep, StringComparison.Ordinal);
        Assert.Contains("stratalint-canonical-lean-report-v2-", restoreStep, StringComparison.Ordinal);
        Assert.Contains("steps.report-cache.outputs.cache-hit == 'true'", reuseStep, StringComparison.Ordinal);
        Assert.Contains("steps.report-reuse.outcome != 'success'", productionStep, StringComparison.Ordinal);
        Assert.Contains("lean-report-ci-baseline.sh", productionStep, StringComparison.Ordinal);
        Assert.Contains("export STRATALINT_REPORT_CACHE_ROOT=", productionStep, StringComparison.Ordinal);
        Assert.Contains("|| true)", productionStep, StringComparison.Ordinal);
        Assert.DoesNotContain("modules.tsv", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("--module-cache-report", productionStep, StringComparison.Ordinal);
        Assert.DoesNotContain("--module-cache-manifest", productionStep, StringComparison.Ordinal);
        Assert.DoesNotContain("--module-cache-report", pair, StringComparison.Ordinal);
        Assert.DoesNotContain("--module-cache-manifest", pair, StringComparison.Ordinal);
        Assert.DoesNotContain("--modules-file", pair, StringComparison.Ordinal);
        Assert.Contains(".materials.zip", reuseStep, StringComparison.Ordinal);
        Assert.Contains(".materials.zip", stagingStep, StringComparison.Ordinal);
        Assert.Contains(".logs", stagingStep, StringComparison.Ordinal);
        LeanReportCiBaselineScriptContract.AssertTrustedStagingAndFailClosedFallbacks();
    }

}
