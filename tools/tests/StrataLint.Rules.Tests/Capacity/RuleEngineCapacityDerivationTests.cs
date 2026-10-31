using StrataLint.Engine;

namespace StrataLint.Rules.Tests;

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
        var deltaFinding = Assert.Single(delta.Diagnostics);
        Assert.Equal(RuleFixture.RingPath, deltaFinding.Path);
        Assert.Equal(AdmissionEffect.Block, deltaFinding.AdmissionEffect);
        Assert.Contains("lines (hard limit 1000)", deltaFinding.Message, StringComparison.Ordinal);
        var current = RuleCatalog.Default.EvaluateCurrentSingle(RuleId.CreateKnown(3), context.CurrentFacts);
        var finding = Assert.Single(current.Diagnostics, item => item.Path == RuleFixture.RingPath);
        Assert.Equal($"artifact exceeds {RepositoryRules.ArtifactHardLineLimit} lines", finding.Message);
    }

}
