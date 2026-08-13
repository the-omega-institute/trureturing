namespace StrataLint.Tests;

public sealed class TestSplitCallSiteTests
{
    [Fact]
    public void EveryEngineeringTestCallSiteUsesTheUnfilteredAllTarget()
    {
        var root = FindRepositoryRoot();
        var workflow = File.ReadAllText(Path.Combine(root, ".github", "workflows", "ci.yml"));
        var preflight = File.ReadAllText(Path.Combine(root, "Meta/StrataLint/scripts/preflight.sh"));
        var localGate = File.ReadAllText(Path.Combine(root, "Meta/StrataLint/scripts/local-harness-gate.sh"));

        Assert.Contains("make -C candidate test-all", workflow, StringComparison.Ordinal);
        Assert.Contains("CI=true STRATALINT_REQUIRE_LIVE_REPORT=1 make test-all", preflight, StringComparison.Ordinal);
        Assert.Contains("run_stage engineering-test make -C \"$CANDIDATE_ROOT\" test-all", localGate, StringComparison.Ordinal);
        Assert.DoesNotContain("make -C candidate test\n", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("STRATALINT_REQUIRE_LIVE_REPORT=1 make test\n", preflight, StringComparison.Ordinal);
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
