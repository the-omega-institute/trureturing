using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class R13ScopeNarrowingTests
{
    private const string UnrelatedDelta = "docs/reports/r13-probe.json";
    private const string OldInvalidPath = "legacy-invalid/old.txt";
    private const string OldMalformedJson = "Evidence/D5/S0/Carrier/Old.run.json";
    private const string OldMirrorSource = RuleFixture.RingPath;

    [Fact]
    [BaseFactScopeProbe(
        15,
        typeof(RepositoryPathPolicy),
        nameof(RepositoryPathPolicy.EvaluatePathFindings))]
    public void Sl015EvaluatePathFindingsScopesHistoricalPathFinding() =>
        Sl015AdditionalEdgeScopeTests.RunEvaluatePathFindingsScopeProbe();

    [Fact]
    [BaseFactScopeProbe(
        15,
        typeof(RepositoryRules),
        nameof(RepositoryRules.GidCharacterSet))]
    public void Sl015GidCharacterSetScopesLocalFindingToDeltaAndImplementationClosure()
    {
        var unrelated = FixtureWithInvalidOldGid();
        var unrelatedResult = Execute(unrelated, UnrelatedDelta);
        Assert.DoesNotContain(
            unrelatedResult.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(15)
                && diagnostic.Path == OldMirrorSource
                && diagnostic.Message == "GID violates the machine-field character set");

        var changed = FixtureWithInvalidOldGid();
        var changedResult = Execute(changed, OldMirrorSource);
        Assert.Contains(
            changedResult.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(15)
                && diagnostic.Path == OldMirrorSource
                && diagnostic.Message == "GID violates the machine-field character set");

        var implementation = FixtureWithInvalidOldGid();
        var implementationResult = Execute(
            implementation,
            "tools/StrataLint.Engine/Rules/RepositoryRules.Content.cs");
        Assert.Contains(
            implementationResult.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(15)
                && diagnostic.Path == OldMirrorSource
                && diagnostic.Message == "GID violates the machine-field character set");
    }

    [Fact]
    public void Sl015FormulaParserRevalidatesStoredFormulaWhenItsImplementationChanges()
    {
        const string formulaPath = "Evidence/D5/S0/Carrier/Formula.check.json";
        var fixture = new RuleFixture();
        fixture.Files[formulaPath] = "{\"formula\":\"sqrt@5\",\"refs\":{}}\n";
        fixture.Baseline[formulaPath] = fixture.Files[formulaPath];
        fixture.ForkPoint[formulaPath] = fixture.Files[formulaPath];

        var result = Execute(
            fixture,
            "tools/StrataLint.Engine/Rules/RepositoryRules.Formulas.cs");

        Assert.Contains(
            result.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(15)
                && diagnostic.Path == formulaPath
                && diagnostic.Message.Contains("illegal formula character", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl015SuppressesHistoricalDuplicateGidFindingForUnrelatedDelta()
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.BlueprintPath] = fixture.Files[RuleFixture.RingPath];
        fixture.Baseline[RuleFixture.BlueprintPath] = fixture.Files[RuleFixture.RingPath];
        fixture.ForkPoint[RuleFixture.BlueprintPath] = fixture.Files[RuleFixture.RingPath];

        var result = Execute(fixture, UnrelatedDelta);

        Assert.DoesNotContain(
            result.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(15)
                && diagnostic.Message.Contains("duplicate GID", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl000ScopesOldPathDiagnosticsButRetainsChangedAndImplementationCases()
    {
        var unrelated = FixtureWithOldInvalidPath();
        var unrelatedResult = Execute(unrelated, UnrelatedDelta);
        Assert.DoesNotContain(
            unrelatedResult.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(0)
                && diagnostic.Path == OldInvalidPath);

        var changed = FixtureWithOldInvalidPath();
        var changedResult = Execute(changed, OldInvalidPath);
        Assert.Contains(
            changedResult.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(0)
                && diagnostic.Path == OldInvalidPath);

        var implementation = FixtureWithOldInvalidPath();
        var implementationResult = Execute(
            implementation,
            "tools/StrataLint.Engine/Rules/RepositoryRules.cs");
        Assert.Contains(
            implementationResult.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(0)
                && diagnostic.Path == OldInvalidPath);
    }

    [Fact]
    [BaseFactScopeProbe(4)]
    public void Sl004ScopesUnchangedMirrorPairButKeepsDeltaAndImplementationPairs()
    {
        var unrelated = new RuleFixture();
        RemoveBlueprintMirror(unrelated);
        var unrelatedResult = Execute(unrelated, "Evidence/D5/S0/Carrier/Delta.check.json");
        Assert.DoesNotContain(
            unrelatedResult.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(4)
                && diagnostic.Path == OldMirrorSource
                && diagnostic.Message.Contains("missing mirror", StringComparison.Ordinal));

        var changed = new RuleFixture();
        RemoveBlueprintMirror(changed);
        var changedResult = Execute(changed, OldMirrorSource);
        Assert.Contains(
            changedResult.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(4)
                && diagnostic.Path == OldMirrorSource
                && diagnostic.Message.Contains("missing mirror", StringComparison.Ordinal));

        var implementation = new RuleFixture();
        RemoveBlueprintMirror(implementation);
        var implementationResult = Execute(
            implementation,
            "tools/StrataLint.Engine/Rules/RepositoryRules.Structure.cs");
        Assert.Contains(
            implementationResult.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(4)
                && diagnostic.Path == OldMirrorSource
                && diagnostic.Message.Contains("missing mirror", StringComparison.Ordinal));

        var targetChanged = new RuleFixture();
        RemoveBlueprintMirror(targetChanged);
        var targetResult = Execute(targetChanged, RuleFixture.BlueprintPath);
        Assert.Contains(
            targetResult.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(4)
                && diagnostic.Path == OldMirrorSource
                && diagnostic.Message.Contains("missing mirror", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl019ScopesOldJsonParseFindingButKeepsChangedAndImplementationCases()
    {
        var unrelated = FixtureWithOldMalformedJson();
        var unrelatedResult = Execute(unrelated, UnrelatedDelta);
        Assert.DoesNotContain(
            unrelatedResult.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(19)
                && diagnostic.Path == OldMalformedJson
                && diagnostic.Message == "structured anomaly scan cannot parse JSON");

        var changed = FixtureWithOldMalformedJson();
        var changedResult = Execute(changed, OldMalformedJson);
        Assert.Contains(
            changedResult.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(19)
                && diagnostic.Path == OldMalformedJson
                && diagnostic.Message == "structured anomaly scan cannot parse JSON");

        var implementation = FixtureWithOldMalformedJson();
        var implementationResult = Execute(
            implementation,
            "tools/StrataLint.Engine/Rules/RepositoryRules.StructuredScan.cs");
        Assert.Contains(
            implementationResult.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(19)
                && diagnostic.Path == OldMalformedJson
                && diagnostic.Message == "structured anomaly scan cannot parse JSON");
    }

    [Fact]
    public void Sl019StillConsumesOldJsonWhenLeanTaskDeltaChanges()
    {
        var fixture = new RuleFixture();
        const string task = "D5-T0099";
        fixture.Baseline[RuleFixture.RingPath] += $"/-- TASK {task}\n    historical task. -/\n";
        fixture.ForkPoint[RuleFixture.RingPath] = fixture.Baseline[RuleFixture.RingPath];
        fixture.Files[OldMalformedJson] = $"{{\"anomaly\":\"open\",\"case_id\":\"{task}\"}}\n";
        fixture.Baseline[OldMalformedJson] = fixture.Files[OldMalformedJson];
        fixture.ForkPoint[OldMalformedJson] = fixture.Files[OldMalformedJson];

        var result = Execute(fixture, RuleFixture.RingPath);

        Assert.Contains(
            result.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(19)
                && diagnostic.Path == OldMalformedJson
                && diagnostic.Message.Contains("unledgered anomaly", StringComparison.Ordinal));
    }

    [Fact]
    public void Sl019DoesNotReplayOldJsonWhenLeanDeltaPreservesTaskSet()
    {
        var fixture = new RuleFixture();
        const string task = "D5-T0099";
        fixture.Files[RuleFixture.RingPath] += "\n-- theorem-only candidate delta\n";
        fixture.Files[OldMalformedJson] = $"{{\"anomaly\":\"open\",\"case_id\":\"{task}\"}}\n";
        fixture.Baseline[OldMalformedJson] = fixture.Files[OldMalformedJson];
        fixture.ForkPoint[OldMalformedJson] = fixture.Files[OldMalformedJson];

        var result = Execute(fixture, RuleFixture.RingPath);

        Assert.DoesNotContain(
            result.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(19)
                && diagnostic.Path == OldMalformedJson
                && diagnostic.Message.Contains("unledgered anomaly", StringComparison.Ordinal));
    }

    [Fact]
    public void HeartsLedgerParserRevalidatesStoredLedgerWhenItsImplementationChanges()
    {
        var fixture = new RuleFixture();
        var malformed = HeartsAuthorizationLedger.Header + "not a ledger row\n";
        fixture.Files[HeartsAuthorizationLedger.Path] = malformed;
        fixture.Baseline[HeartsAuthorizationLedger.Path] = malformed;
        fixture.ForkPoint[HeartsAuthorizationLedger.Path] = malformed;

        var result = Execute(
            fixture,
            "tools/StrataLint.Engine/Authorization/HeartsAuthorizationLedger.cs");

        Assert.Contains(
            result.Diagnostics,
            diagnostic => diagnostic.RuleId == RuleId.CreateKnown(8)
                && diagnostic.Path == HeartsAuthorizationLedger.Path
                && diagnostic.Message.Contains("exactly four columns", StringComparison.Ordinal));
    }

    private static RuleFixture FixtureWithInvalidOldGid()
    {
        var fixture = new RuleFixture();
        var invalid = fixture.Files[RuleFixture.RingPath]
            .Replace("D5/S0/Carrier/Ring", "D5/S0/Carrier/Ring@", StringComparison.Ordinal);
        fixture.Files[RuleFixture.RingPath] = invalid;
        fixture.Baseline[RuleFixture.RingPath] = invalid;
        fixture.ForkPoint[RuleFixture.RingPath] = invalid;
        return fixture;
    }

    private static RuleFixture FixtureWithOldInvalidPath()
    {
        var fixture = new RuleFixture();
        fixture.Files[OldInvalidPath] = "legacy\n";
        fixture.Baseline[OldInvalidPath] = fixture.Files[OldInvalidPath];
        fixture.ForkPoint[OldInvalidPath] = fixture.Files[OldInvalidPath];
        return fixture;
    }

    private static RuleFixture FixtureWithOldMalformedJson()
    {
        var fixture = new RuleFixture();
        fixture.Files[OldMalformedJson] = "{\"anomaly\":\n";
        fixture.Baseline[OldMalformedJson] = fixture.Files[OldMalformedJson];
        fixture.ForkPoint[OldMalformedJson] = fixture.Files[OldMalformedJson];
        return fixture;
    }

    private static void RemoveBlueprintMirror(RuleFixture fixture)
    {
        fixture.Files.Remove(RuleFixture.BlueprintPath);
        fixture.Baseline.Remove(RuleFixture.BlueprintPath);
        fixture.ForkPoint.Remove(RuleFixture.BlueprintPath);
    }

    private static CompletedRuleSet Execute(RuleFixture fixture, string changedPath) =>
        Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build(RawChangeSet.Create([changedPath])))).Capability;
}
