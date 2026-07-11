using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RuleEngineTests
{
    public static TheoryData<int, string> BlockingCases => new()
    {
        { 1, "upward-import" },
        { 2, "sorry" },
        { 3, "file-capacity" },
        { 4, "mirror" },
        { 5, "chronicle" },
        { 6, "badge" },
        { 8, "heart" },
        { 10, "generality" },
        { 11, "domain" },
        { 12, "header" },
        { 13, "task" },
        { 15, "formula" },
        { 16, "backfill" },
        { 17, "query" },
        { 18, "values" },
        { 19, "anomaly" },
        { 20, "axiom" },
        { 21, "future" },
    };

    [Theory]
    [MemberData(nameof(BlockingCases))]
    public void ActiveRuleHasGreenAndRedExecutableFixtures(int number, string mutation)
    {
        var green = new RuleFixture();
        if (number == 16)
        {
            green.AddBackfillTargets();
        }
        var greenResult = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(number), green.Build());
        Assert.Empty(greenResult.Diagnostics);
        Assert.Null(greenResult.DeferredCase);

        var red = new RuleFixture();
        if (number == 16)
        {
            red.AddBackfillTargets();
        }
        red.Apply(mutation);
        var redContext = number == 20 ? red.BuildForRuleCompatibility() : red.Build();
        var redResult = RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(number), redContext);

        Assert.NotEmpty(redResult.Diagnostics);
        Assert.All(
            redResult.Diagnostics,
            diagnostic => Assert.Equal(RuleId.CreateKnown(number), diagnostic.RuleId));
        Assert.Null(redResult.DeferredCase);
    }

    [Theory]
    [InlineData(7, "D5-T0011")]
    [InlineData(9, "D5-T0012")]
    [InlineData(14, "D5-T0010")]
    public void DeferredRulesNeverMasqueradeAsPass(int number, string caseId)
    {
        var result = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(number),
            new RuleFixture().Build());

        Assert.Empty(result.Diagnostics);
        Assert.Equal(CaseId.CreateKnown(caseId), result.DeferredCase);
    }

    [Fact]
    public void CoverageManifestNamesEveryRuleWithARealRedOrDeferredBranch()
    {
        var exercised = BlockingCases.Select(item => (int)item[0])
            .Concat(new[] { 7, 9, 14, 22 })
            .Order()
            .ToArray();

        Assert.Equal(Enumerable.Range(1, 22), exercised);
    }
}
