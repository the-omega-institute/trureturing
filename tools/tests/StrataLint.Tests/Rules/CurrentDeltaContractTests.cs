using System.Reflection;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CurrentDeltaContractTests
{
    [Fact]
    public void CurrentContextHasNoHistoryCapabilities()
    {
        var history = typeof(CurrentRuleContext).FindMembers(MemberTypes.Property,
            BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic,
            static (member, _) => member.Name is "Baseline" or "Changes" or "RuleImplementationChanged", null);
        Assert.Empty(history);
        Assert.False(typeof(CurrentRuleContext).IsAssignableFrom(typeof(DeltaRuleContext)));
    }

    [Fact]
    public void CurrentJudgesExistingInvalidSourceWithoutChanges()
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] = "def invalidHeader : Nat := 0\n";
        fixture.Changes.Clear();
        var data = fixture.BuildForRuleCompatibility();
        var context = CurrentRuleContext.Create(data.Current, data.Policy, data.Lean);
        var result = RuleCatalog.Default.EvaluateCurrentSingle(RuleId.CreateKnown(12), context);
        Assert.Contains(result.Diagnostics, finding => finding.Path == RuleFixture.RingPath);
    }

    [Theory]
    [InlineData(16)]
    [InlineData(30)]
    [InlineData(31)]
    [InlineData(32)]
    [InlineData(33)]
    [InlineData(34)]
    public void HistoricalAdmissionScopesRemainDeltaOnly(int rule)
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.BlueprintSourcePath] = "// issue #123, digestion atom_id\n";
        fixture.Files["tools/scripts/workflow/bad.sh"] = "git show old:program | bash\n";
        fixture.Files[RuleFixture.FixtureBackfillAtomPath] = "not valid yaml: [\n";
        var data = fixture.BuildForRuleCompatibility();
        var current = CurrentRuleContext.Create(data.Current, data.Policy, data.Lean);
        Assert.Empty(RuleCatalog.Default.EvaluateCurrentSingle(RuleId.CreateKnown(rule), current).Diagnostics);
    }

    [Fact]
    public void ComposedEvaluationMatchesCurrentPlusDeltaWithoutDuplicateFindings()
    {
        var fixture = new RuleFixture();
        fixture.ChangeHeartSignature();
        var delta = fixture.BuildForRuleCompatibility(RawChangeSet.Create(fixture.Changes));
        var current = CurrentRuleContext.Create(delta.Current, delta.Policy, delta.Lean);
        var id = RuleId.CreateKnown(8);
        var common = RuleCatalog.Default.EvaluateCurrentSingle(id, current).Diagnostics;
        var differences = RuleCatalog.Default.EvaluateDeltaSingle(id, delta).Diagnostics;
        var composed = RuleCatalog.Default.EvaluateSingle(id, delta).Diagnostics;
        Assert.Equal(common.Concat(differences).ToArray(), composed.ToArray());
        Assert.Single(differences, finding => finding.Path == RuleFixture.HeartsPath);
    }
}
