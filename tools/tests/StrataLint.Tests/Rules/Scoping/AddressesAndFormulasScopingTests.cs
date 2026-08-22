using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class AddressesAndFormulasScopingTests
{
    private const string FormulaPath = "Evidence/D5/S0/Carrier/Formula.check.json";
    private const string UnrelatedPath = "notes/unrelated.txt";

    [Fact]
    [BaseFactScopeProbe(
        15,
        typeof(RepositoryRules),
        nameof(RepositoryRules.FormulaValidation))]
    public void Sl015FormulaValidationDoesNotRevalidateMalformedFormulaOutsideCandidateDelta()
    {
        var fixture = new RuleFixture();
        SetOldSnapshotFile(fixture, FormulaPath, "{\"formula\":\"sqrt@5\",\"refs\":{}}\n");
        SetUnrelatedDelta(fixture);

        var completed = Execute(fixture, UnrelatedPath);

        Assert.Contains(RuleId.CreateKnown(15), completed.ExecutedRules);
        Assert.DoesNotContain(completed.Diagnostics, diagnostic => diagnostic.Path == FormulaPath);

        var changed = new RuleFixture();
        changed.Baseline[FormulaPath] = "{\"formula\":\"5\",\"refs\":{}}\n";
        changed.ForkPoint[FormulaPath] = changed.Baseline[FormulaPath];
        changed.Files[FormulaPath] = "{\"formula\":\"sqrt@5\",\"refs\":{}}\n";
        Assert.Contains(Execute(changed, FormulaPath).Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(15)
            && diagnostic.Path == FormulaPath
            && diagnostic.Message.Contains("illegal formula character", StringComparison.Ordinal));

        var implementation = new RuleFixture();
        SetOldSnapshotFile(implementation, FormulaPath, "{\"formula\":\"sqrt@5\",\"refs\":{}}\n");
        Assert.Contains(
            Execute(implementation, "tools/StrataLint.Engine/Rules/RepositoryRules.Formulas.cs").Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(15)
                && diagnostic.Path == FormulaPath
                && diagnostic.Message.Contains("illegal formula character", StringComparison.Ordinal));
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
    public void Sl015SuppressesHistoricalDuplicateGidForUnrelatedCandidateDelta()
    {
        var fixture = new RuleFixture();
        SetOldSnapshotFile(fixture, RuleFixture.BlueprintPath, fixture.Files[RuleFixture.RingPath]);
        SetUnrelatedDelta(fixture);

        var completed = Execute(fixture, UnrelatedPath);

        Assert.DoesNotContain(completed.Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(15)
            && diagnostic.Message.Contains("duplicate GID", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl015SuppressesHistoricalEvidenceSelectorCollisionForUnrelatedCandidateDelta()
    {
        const string jsonPath = "Evidence/D5/S0/Carrier/Probe.result.json";
        const string yamlPath = "Evidence/D5/S0/Carrier/Probe.result.yaml";
        var fixture = new RuleFixture();
        SetOldSnapshotFile(fixture, jsonPath, "{}\n");
        SetOldSnapshotFile(fixture, yamlPath, "value: fixture\n");
        SetUnrelatedDelta(fixture);

        var completed = Execute(fixture, UnrelatedPath);

        Assert.DoesNotContain(completed.Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(15)
            && diagnostic.Message.Contains(
                "evidence selector has multiple artifact kinds",
                StringComparison.Ordinal));
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
