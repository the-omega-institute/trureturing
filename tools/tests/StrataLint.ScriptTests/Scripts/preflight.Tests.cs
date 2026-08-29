using StrataLint.Engine;

namespace StrataLint.ScriptTests;

[ScriptSubject("tools/scripts/preflight.sh")]
public sealed partial class PreflightScriptTests
{
    private const string PreflightScriptPath = "tools/scripts/preflight.sh";

    [Fact]
    public void PreflightRefreshesLeanReportAfterDotnetAndBeforeTests()
    {
        var preflight = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/scripts/preflight.sh"));

        var dotnetIndex = preflight.IndexOf("CI=true make -C tools dotnet", StringComparison.Ordinal);
        var leanReportIndex = preflight.IndexOf("make lean-report", StringComparison.Ordinal);
        var testIndex = preflight.IndexOf(
            "CI=true STRATALINT_REQUIRE_LIVE_REPORT=1 make -C tools engineering-tests",
            StringComparison.Ordinal);

        Assert.True(dotnetIndex >= 0, "preflight must build the .NET report consumer");
        Assert.True(leanReportIndex >= 0, "preflight must refresh the raw Lean report");
        Assert.True(testIndex >= 0, "preflight must run the harness tests");
        Assert.True(dotnetIndex < leanReportIndex, "the .NET build must precede report production");
        Assert.True(leanReportIndex < testIndex, "report production must precede every test consumer");
    }

    [Fact]
    public void EngineeringScopeUsesTheMergeResultAndItsFirstParent()
    {
        var preflight = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/scripts/preflight.sh"));

        Assert.Contains("ENGINEERING_HEAD=\"$(git rev-parse HEAD)\"", preflight, StringComparison.Ordinal);
        Assert.Contains("ENGINEERING_BASE=\"$(git rev-parse HEAD^1)\"", preflight, StringComparison.Ordinal);
    }
}
