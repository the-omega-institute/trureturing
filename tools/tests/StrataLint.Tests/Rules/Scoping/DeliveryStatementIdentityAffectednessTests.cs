using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DeliveryStatementIdentityAffectednessTests
{
    [Theory]
    [InlineData("docs/MISSION.md")]
    [InlineData(RuleFixture.RingPath)]
    [InlineData("Golden/Frozen/accepted/fixture-event.json")]
    public void DeliveryStatementIdentitySkipsValidationInputsWithoutAFrontierDeletion(string path)
    {
        var fixture = new RuleFixture();
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(RawChangeSet.Create([path])))).Capability;

        Assert.DoesNotContain(RuleId.CreateKnown(27), completed.ExecutedRules);
    }

    [Fact]
    public void DeliveryStatementIdentitySkipsAModifiedFrontierSourceWhoseStatementShaDidNotChange()
    {
        const string path = "D5/X_Frontier/PrimeNormIrreducibility.lean";
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            baselineOwnerKind: "declaration-ready-mathematical-open",
            baselineIncludeContract: true);

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(RawChangeSet.Create([path])))).Capability;

        Assert.DoesNotContain(RuleId.CreateKnown(27), completed.ExecutedRules);
    }

    [Fact]
    [BaseFactScopeProbe(27)]
    public void Sl027DeliveryStatementIdentityExecutesWhenAnExistingFrontierStatementShaChanges()
    {
        const string path = "D5/X_Frontier/PrimeNormIrreducibility.lean";
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            baselineOwnerKind: "declaration-ready-mathematical-open",
            baselineIncludeContract: true);
        fixture.ReviseTheoristStatementWithoutRevision();

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(RawChangeSet.Create([path])))).Capability;

        Assert.Contains(RuleId.CreateKnown(27), completed.ExecutedRules);
    }

    [Fact]
    public void DeliveryStatementIdentitySkipsANewFrontierContract()
    {
        const string path = "D5/X_Frontier/PrimeNormIrreducibility.lean";
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget("prime-norm-irreducibility");

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(RawChangeSet.Create([path])))).Capability;

        Assert.DoesNotContain(RuleId.CreateKnown(27), completed.ExecutedRules);
    }

    [Fact]
    public void Sl027DeliveryStatementIdentityExecutesWhenABaselineFrontierSourceIsDeleted()
    {
        const string path = "D5/X_Frontier/PrimeNormIrreducibility.lean";
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            baselineOwnerKind: "declaration-ready-mathematical-open",
            baselineIncludeContract: true);
        fixture.ReplaceRetiredBaselineWithLiteralV2Contract();
        fixture.RetireTheoristTarget();

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(RawChangeSet.Create([path])))).Capability;

        Assert.Contains(RuleId.CreateKnown(27), completed.ExecutedRules);
    }
}
