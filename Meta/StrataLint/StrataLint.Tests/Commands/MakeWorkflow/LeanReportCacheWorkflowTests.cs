namespace StrataLint.Tests;

public sealed class LeanReportCacheWorkflowTests
{
    private const string AdmissionWorkflowPath = ".github/workflows/ci.yml";
    private static readonly string PairScriptPath = string.Join(
        '/', "Meta", "StrataLint", "scripts", "lean-report-pair.sh");

    [Fact]
    public void ContentAddressedReuseHasNoPrefixFallback()
    {
        var root = FindRepositoryRoot();
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
