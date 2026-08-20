using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class AddressesAndFormulasScopingTests
{
    private const string FormulaPath = "Evidence/D5/S0/Carrier/Formula.check.json";
    private const string UnrelatedPath = "notes/unrelated.txt";

    [Fact]
    public void Sl015DoesNotRevalidateMalformedFormulaOutsideCandidateDelta()
    {
        var fixture = new RuleFixture();
        SetOldSnapshotFile(fixture, FormulaPath, "{\"formula\":\"sqrt@5\",\"refs\":{}}\n");
        SetUnrelatedDelta(fixture);

        var completed = Execute(fixture, UnrelatedPath);

        Assert.Contains(RuleId.CreateKnown(15), completed.ExecutedRules);
        Assert.DoesNotContain(completed.Diagnostics, diagnostic => diagnostic.Path == FormulaPath);
    }

    [Fact]
    public void Sl015StillValidatesMalformedFormulaInsideCandidateDelta()
    {
        var fixture = new RuleFixture();
        fixture.Baseline[FormulaPath] = "{\"formula\":\"5\",\"refs\":{}}\n";
        fixture.ForkPoint[FormulaPath] = fixture.Baseline[FormulaPath];
        fixture.Files[FormulaPath] = "{\"formula\":\"sqrt@5\",\"refs\":{}}\n";

        var completed = Execute(fixture, FormulaPath);

        Assert.Contains(completed.Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(15)
            && diagnostic.Path == FormulaPath
            && diagnostic.Message.Contains("illegal formula character", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl015KeepsGlobalDuplicateGidQueryForUnrelatedCandidateDelta()
    {
        var fixture = new RuleFixture();
        SetOldSnapshotFile(fixture, RuleFixture.BlueprintPath, fixture.Files[RuleFixture.RingPath]);
        SetUnrelatedDelta(fixture);

        var completed = Execute(fixture, UnrelatedPath);

        Assert.Contains(completed.Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(15)
            && diagnostic.Message.Contains("duplicate GID", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl015KeepsGlobalEvidenceSelectorQueryForUnrelatedCandidateDelta()
    {
        const string jsonPath = "Evidence/D5/S0/Carrier/Probe.result.json";
        const string yamlPath = "Evidence/D5/S0/Carrier/Probe.result.yaml";
        var fixture = new RuleFixture();
        SetOldSnapshotFile(fixture, jsonPath, "{}\n");
        SetOldSnapshotFile(fixture, yamlPath, "value: fixture\n");
        SetUnrelatedDelta(fixture);

        var completed = Execute(fixture, UnrelatedPath);

        Assert.Equal(
            2,
            completed.Diagnostics.Count(diagnostic =>
                diagnostic.RuleId == RuleId.CreateKnown(15)
                && diagnostic.Message.Contains(
                    "evidence selector has multiple artifact kinds",
                    StringComparison.Ordinal)));
    }

    private static CompletedRuleSet Execute(RuleFixture fixture, string changedPath) =>
        Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(RawChangeSet.Create([changedPath])))).Capability;

    private static void SetOldSnapshotFile(RuleFixture fixture, string path, string text)
    {
        fixture.Files[path] = text;
        fixture.Baseline[path] = text;
        fixture.ForkPoint[path] = text;
    }

    private static void SetUnrelatedDelta(RuleFixture fixture)
    {
        fixture.Baseline[UnrelatedPath] = "old\n";
        fixture.ForkPoint[UnrelatedPath] = "old\n";
        fixture.Files[UnrelatedPath] = "candidate\n";
    }
}
