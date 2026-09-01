using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DigestionAtomsAppendOnlyTests
{
    private const int RuleNumber = 30;
    private const string RuleImplementationPath =
        "tools/StrataLint.Engine/Rules/RepositoryRules.Structure.cs";
    private const string ReplacementHash =
        "0000000000000000000000000000000000000000000000000000000000000000";

    [Fact]
    [BaseFactScopeProbe(RuleNumber)]
    public void Sl030DigestionAtomsAppendOnlyScopesContentHashesAndKeepsImplementationRechecks()
    {
        var unrelated = DroppedBaseContent();
        Assert.Empty(Evaluate(unrelated, RuleFixture.BlueprintPath).Diagnostics);

        var changed = DroppedBaseContent();
        Assert.Single(Evaluate(changed, RuleFixture.FixtureBackfillAtomPath).Diagnostics);

        var implementation = DroppedBaseContent();
        Assert.Single(Evaluate(implementation, RuleImplementationPath).Diagnostics);
    }

    private static RuleFixture DroppedBaseContent()
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.FixtureBackfillAtomPath] = fixture.Files[
                RuleFixture.FixtureBackfillAtomPath]
            .Replace(RuleFixture.FixtureAtomId, ReplacementHash, StringComparison.Ordinal);
        return fixture;
    }

    private static SingleRuleEvaluation Evaluate(RuleFixture fixture, string changedPath) =>
        RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(RuleNumber),
            fixture.Build(changes: RawChangeSet.Create([changedPath])));
}
