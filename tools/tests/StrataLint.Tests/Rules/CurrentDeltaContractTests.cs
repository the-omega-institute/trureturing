using System.Reflection;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CurrentDeltaContractTests
{
    private static string[] CurrentIds => ["SL-001", "SL-002", "SL-003", "SL-004", "SL-006", "SL-008", "SL-010", "SL-011", "SL-012", "SL-015", "SL-017", "SL-018", "SL-019", "SL-020", "SL-021", "SL-023", "SL-025", "SL-026"];

    [Theory]
    [InlineData("SL-012")]
    [InlineData("SL-015")]
    public void ValidatedSelectionRetainsAllDiagnosticsOfItsPredicate(string id)
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] = "def invalidHeader : Nat := 0\n";
        fixture.Files["D5/illegal name.lean"] = "def invalid : Nat := 0\n";
        var data = fixture.BuildForRuleCompatibility();
        var full = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.ExecuteCurrent(
            CurrentRuleContext.Create(data.Current, data.Policy, data.Lean))).Capability;
        var selected = Assert.IsType<RuleExecutionOutcome.Completed>(RuleCatalog.Default.ExecuteCurrent(
            CurrentRuleContext.Create(data.Current, data.Policy, data.Lean, null,
                CurrentRuleSelection.Create(CurrentIds, [id])))).Capability;
        Assert.Equal(new[] { id }, selected.ExecutedRules.Select(rule => rule.Value));
        Assert.Equal(full.Diagnostics.Where(d => d.RuleId.Value == id || id == "SL-015" && d.RuleId.Value == "SL-000"), selected.Diagnostics);
        Assert.NotEmpty(selected.Diagnostics);
        Assert.Equal(full.DeferredRules.ToArray(), selected.DeferredRules.ToArray());
    }

    [Fact]
    public void SelectionRejectsMissingDuplicateAndUnregisteredPredicates()
    {
        Assert.Throws<InvalidDataException>(() => CurrentRuleSelection.Create(CurrentIds.Skip(1).ToArray(), []));
        Assert.Throws<InvalidDataException>(() => CurrentRuleSelection.Create(CurrentIds.Append("SL-001").ToArray(), []));
        Assert.Throws<InvalidDataException>(() => CurrentRuleSelection.Create(CurrentIds, ["SL-999"]));
    }

    [Fact]
    public void ValidatedScribeMaterialRoundTripsAndRejectsChangedDefinitions()
    {
        var fixture = new RuleFixture();
        var data = fixture.BuildForRuleCompatibility();
        var empty = VerifiedScribeEmissions.Empty.WriteMaterial();
        var emptySnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawRepositorySnapshot.Create([]))).Snapshot;
        var restored = VerifiedScribeEmissions.ReadMaterial(empty, emptySnapshot);
        Assert.Empty(restored.DescribeLatexRecords);
        Assert.ThrowsAny<Exception>(() => VerifiedScribeEmissions.ReadMaterial("{}", data.Current));
    }

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
