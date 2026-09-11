using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RuleEngineCapacityDerivationTests
{
    [Fact]
    public void Sl003D5OnlyDeltaSkipsUnknownDebtDerivationAndStillNamesCapacityFinding()
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] += string.Concat(
            Enumerable.Repeat("-- pad\n", RepositoryRules.ArtifactHardLineLimit + 1));
        var context = fixture.Build(RawChangeSet.Create([RuleFixture.RingPath]));

        var delta = RuleCatalog.Default.EvaluateDeltaSingle(RuleId.CreateKnown(3), context);
        Assert.Empty(delta.Diagnostics);
        var current = RuleCatalog.Default.EvaluateCurrentSingle(RuleId.CreateKnown(3), context.CurrentFacts);
        var finding = Assert.Single(current.Diagnostics, item => item.Path == RuleFixture.RingPath);
        Assert.Equal("artifact exceeds 800 lines", finding.Message);
    }

}
