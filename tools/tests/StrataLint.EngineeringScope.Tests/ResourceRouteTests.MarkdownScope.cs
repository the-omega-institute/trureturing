using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class ResourceRouteTests
{
    [Fact]
    public void PlannedMarkdownScopeUsesOnlyChangedPathsAndCannotSeedWholeCurrent()
    {
        const string changed = "Blueprint/D5/Changed.md";
        const string unchanged = "Blueprint/D5/Unchanged.md";
        using var fixture = new ResourceFixture(["scribe"], changed);
        fixture.Write(unchanged, "unchanged document");
        fixture.CommitPlan();
        fixture.Processes();
        string[] ids = ["scribe-describe", "scribe-markdown", "scribe-projections"];
        var build = CommonExecutionEvidence.ValidateBuild(fixture.Root);
        var checks = CommonExecutionEvidence.BeginChecks(fixture.Root, "current", build, TextWriter.Null, ids);
        Assert.False(checks.MarkdownScope!.WholeTree);
        Assert.Equal(new[] { changed }, checks.MarkdownScope.Paths);

        fixture.CompleteCheckBoundary(ids);
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
        var warm = CommonExecutionEvidence.BeginChecks(fixture.Root, "current", build, TextWriter.Null, ids);
        Assert.False(warm.IsSelected("scribe-markdown"));

        fixture.Processes(bindPlan: false);
        var whole = CommonExecutionEvidence.BeginChecks(fixture.Root, "current",
            CommonExecutionEvidence.ValidateBuild(fixture.Root), TextWriter.Null, ids);
        Assert.True(whole.MarkdownScope!.WholeTree);
        Assert.Equal(new[] { changed, unchanged }, whole.MarkdownScope.Paths);
        Assert.True(whole.IsSelected("scribe-markdown"));
    }
}
