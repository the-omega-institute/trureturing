using System.Reflection;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CurrentDeltaContractTests
{
    [Theory]
    [InlineData("Meta/judge-seed.json", true)]
    [InlineData("Meta/package-materials.json", true)]
    [InlineData("Meta/unregistered.json", false)]
    public void CurrentChecksRealRepositoryMetadataRegistrationWithoutHistory(string path, bool registered)
    {
        var registry = TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create("Meta/registry.yaml"));
        var domains = TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create("Meta/domains.yaml"));
        var material = registered
            ? TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(path))
            : "{}\n";
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create([
                RawRepositoryEntry.FromText("Meta/registry.yaml", registry),
                RawRepositoryEntry.FromText("Meta/domains.yaml", domains),
                RawRepositoryEntry.FromText(path, material),
            ]))).Snapshot;
        var policy = RegistryLoadAssert.Accepted(RegistryLoader.Load(
            Encoding.UTF8.GetBytes(registry), Encoding.UTF8.GetBytes(domains))).Policy;
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(LeanClosureValidator.Validate(
            snapshot, LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>()))).Capability;

        var current = CurrentRuleContext.Create(snapshot, policy, lean);
        var outcome = AdmissionPipeline.CheckCurrent(current);
        Assert.True(outcome is RuleExecutionOutcome.Completed,
            outcome is RuleExecutionOutcome.InfrastructureFailure failure ? failure.Message : outcome.ToString());
        var result = Assert.IsType<RuleExecutionOutcome.Completed>(outcome).Capability;
        Assert.Contains(RuleId.CreateKnown(15), result.ExecutedRules);
        var pathFindings = result.Diagnostics.Where(finding => finding.RuleId == RuleId.CreateKnown(0)).ToArray();

        if (registered)
        {
            Assert.Empty(pathFindings);
        }
        else
        {
            var finding = Assert.Single(pathFindings);
            Assert.Equal("SL-000", finding.RuleId.Value);
            Assert.Equal(path, finding.Path);
            Assert.Equal("unknown Meta artifact", finding.Message);
            Assert.Equal(AdmissionEffect.Block, finding.AdmissionEffect);
        }
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
