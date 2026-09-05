using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class UtilityAdmissionRuleTests
{
    private static readonly RuleId UtilityRuleId = RuleId.CreateKnown(30);

    [Fact]
    public void FirstFreezeWithoutUtilityIsBlocked()
    {
        AssertBlockedObservationPair(
            EvaluateFirstFreeze(utility: null),
            "UTILITY-MISSING",
            "kind=unparsed basis=n/a target=n/a");
    }

    [Fact]
    public void BlockedFirstFreezeStillEmitsObserve()
    {
        var missingReport = new RuleFixture();
        missingReport.Files[RuleFixture.RingPath] = WithUtility(
            missingReport.Files[RuleFixture.RingPath],
            "kind=certified-instance; basis=terminal=task:D5-T0001");
        missingReport.Reports.Remove(RuleFixture.RingPath);

        var cases = new[]
        {
            (
                Diagnostics: EvaluateFirstFreeze(utility: null),
                BlockCode: "UTILITY-MISSING",
                ObservationFields: "kind=unparsed basis=n/a target=n/a"),
            (
                Diagnostics: EvaluateFirstFreeze(
                    "kind=certified-instance; basis=terminal=task:D5-T0001; role=answer"),
                BlockCode: "UTILITY-SYNTAX",
                ObservationFields: "kind=unparsed basis=n/a target=n/a"),
            (
                Diagnostics: EvaluateFirstFreeze(
                    "kind=checker; basis=terminal=task:D5-T0001"),
                BlockCode: "UTILITY-INSTANCE-MISSING",
                ObservationFields: "kind=unparsed basis=n/a target=n/a"),
            (
                Diagnostics: EvaluateFirstFreeze(
                    "kind=numeric-reduction; basis=consumer=D5/S0/Carrier/Ring.goldenRing"),
                BlockCode: "UTILITY-PREMISES-MISSING",
                ObservationFields: "kind=unparsed basis=n/a target=n/a"),
            (
                Diagnostics: EvaluateFirstFreeze(
                    "kind=certified-instance; basis=consumer=D5/S0/Carrier/Ring.missing"),
                BlockCode: "UTILITY-TARGET-DANGLING",
                ObservationFields:
                    "kind=certified-instance basis=consumer target=D5/S0/Carrier/Ring.missing"),
            (
                Diagnostics: EvaluateFirstFreeze(missingReport, validateLean: false),
                BlockCode: "UTILITY-INPUT-UNKNOWN",
                ObservationFields:
                    "kind=certified-instance basis=terminal target=task:D5-T0001"),
            (
                Diagnostics: EvaluateFirstFreeze(AtomUtilityFixture(
                    "sha256:0000000000000000000000000000000000000000000000000000000000000000")),
                BlockCode: "UTILITY-REFUTES-ATOM-NO-COVERAGE",
                ObservationFields:
                    $"kind=bounded-enumeration basis=refutes target=atom:{RuleFixture.FixtureAtomId}"),
            (
                Diagnostics: EvaluateFirstFreeze(
                    "kind=certified-instance; "
                    + "basis=consumer=D5/S0/Carrier/ValuesBinding.fixtureValue"),
                BlockCode: "UTILITY-CONSUMER-UNREACHABLE",
                ObservationFields:
                    "kind=certified-instance basis=consumer "
                    + "target=D5/S0/Carrier/ValuesBinding.fixtureValue"),
        };

        foreach (var testCase in cases)
        {
            AssertBlockedObservationPair(
                testCase.Diagnostics,
                testCase.BlockCode,
                testCase.ObservationFields);
        }
    }

    [Fact]
    public void UnknownUtilityRoleIsRejected()
    {
        AssertBlockedObservationPair(
            EvaluateFirstFreeze(
                "kind=certified-instance; basis=terminal=task:D5-T0001; role=answer"),
            "UTILITY-SYNTAX",
            "kind=unparsed basis=n/a target=n/a");
    }

    [Fact]
    public void PendingConsumerIsRejected()
    {
        AssertBlockedObservationPair(
            EvaluateFirstFreeze(
                "kind=certified-instance; basis=pending-consumer=D5/S0/Carrier/Ring.goldenRing"),
            "UTILITY-SYNTAX",
            "kind=unparsed basis=n/a target=n/a");
    }

    [Fact]
    public void CheckerWithoutInstanceIsBlocked()
    {
        AssertBlockedObservationPair(
            EvaluateFirstFreeze("kind=checker; basis=terminal=task:D5-T0001"),
            "UTILITY-INSTANCE-MISSING",
            "kind=unparsed basis=n/a target=n/a");
    }

    [Fact]
    public void ReductionWithoutPremisesIsBlocked()
    {
        AssertBlockedObservationPair(
            EvaluateFirstFreeze(
                "kind=numeric-reduction; basis=consumer=D5/S0/Carrier/Ring.goldenRing"),
            "UTILITY-PREMISES-MISSING",
            "kind=unparsed basis=n/a target=n/a");
    }

    [Fact]
    public void DanglingConsumerDeclarationIsBlocked()
    {
        var diagnostics = EvaluateFirstFreeze(
            "kind=certified-instance; basis=consumer=D5/S0/Carrier/Ring.missing");

        var diagnostic = Assert.Single(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Block);
        Assert.Contains(
            $"UTILITY-TARGET-DANGLING module={RuleFixture.RingPath}",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains("target=D5/S0/Carrier/Ring.missing", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ConsumerWithoutImportPathIsBlocked()
    {
        var diagnostics = EvaluateFirstFreeze(
            "kind=certified-instance; basis=consumer=D5/S0/Carrier/ValuesBinding.fixtureValue");

        var diagnostic = Assert.Single(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Block);
        Assert.Contains(
            $"UTILITY-CONSUMER-UNREACHABLE module={RuleFixture.RingPath}",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains(
            $"consumer_module={RuleFixture.ValuesBindingPath}",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void SameModuleConsumerIsAllowed()
    {
        var diagnostics = EvaluateFirstFreeze(
            "kind=certified-instance; basis=consumer=D5/S0/Carrier/Ring.goldenRing");

        Assert.DoesNotContain(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Block);
    }

    [Fact]
    public void TransitiveConsumerIsAllowed()
    {
        const string intermediatePath = "D5/S0/Carrier/Intermediate.lean";
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] = WithUtility(
            fixture.Files[RuleFixture.RingPath],
            "kind=certified-instance; basis=consumer=D5/S0/Carrier/ValuesBinding.fixtureValue");
        fixture.Files[intermediatePath] = fixture.Files[RuleFixture.RingPath].Replace(
            "D5/S0/Carrier/Ring",
            "D5/S0/Carrier/Intermediate",
            StringComparison.Ordinal);
        fixture.Reports[RuleFixture.ValuesBindingPath] = fixture.Reports[RuleFixture.ValuesBindingPath] with
        {
            Imports = ["D5.S0.Carrier.Intermediate"],
        };
        fixture.Reports[intermediatePath] = new LeanFileReport(
            ["D5.S0.Carrier.Ring"],
            [new LeanDeclaration("intermediate", "def", "Unit", [])]);

        var diagnostics = EvaluateFirstFreeze(fixture);

        Assert.DoesNotContain(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Block);
    }

    [Fact]
    public void MissingIntermediateReportIsUnknownNotUnreachable()
    {
        const string intermediatePath = "D5/S0/Carrier/Intermediate.lean";
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] = WithUtility(
            fixture.Files[RuleFixture.RingPath],
            "kind=certified-instance; basis=consumer=D5/S0/Carrier/ValuesBinding.fixtureValue");
        fixture.Files[intermediatePath] = fixture.Files[RuleFixture.RingPath].Replace(
            "D5/S0/Carrier/Ring",
            "D5/S0/Carrier/Intermediate",
            StringComparison.Ordinal);
        fixture.Reports[RuleFixture.ValuesBindingPath] = fixture.Reports[RuleFixture.ValuesBindingPath] with
        {
            Imports = ["D5.S0.Carrier.Intermediate"],
        };

        var diagnostics = EvaluateFirstFreeze(fixture, validateLean: false);

        var diagnostic = Assert.Single(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Block);
        Assert.Contains(
            $"UTILITY-INPUT-UNKNOWN module={RuleFixture.RingPath}",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains(
            $"reason=consumer-path-input-missing:{intermediatePath}",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.DoesNotContain(
            "UTILITY-CONSUMER-UNREACHABLE",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void ErroredIntermediateReportCannotProveReachability()
    {
        const string intermediatePath = "D5/S0/Carrier/Intermediate.lean";
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] = WithUtility(
            fixture.Files[RuleFixture.RingPath],
            "kind=certified-instance; basis=consumer=D5/S0/Carrier/ValuesBinding.fixtureValue");
        fixture.Files[intermediatePath] = fixture.Files[RuleFixture.RingPath].Replace(
            "D5/S0/Carrier/Ring",
            "D5/S0/Carrier/Intermediate",
            StringComparison.Ordinal);
        fixture.Reports[RuleFixture.ValuesBindingPath] = fixture.Reports[RuleFixture.ValuesBindingPath] with
        {
            Imports = ["D5.S0.Carrier.Intermediate"],
        };
        fixture.Reports[intermediatePath] = new LeanFileReport(
            ["D5.S0.Carrier.Ring"],
            [],
            Error: "synthetic elaboration failure");

        var diagnostics = EvaluateFirstFreeze(fixture, validateLean: false);

        var diagnostic = Assert.Single(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Block);
        Assert.Contains(
            $"UTILITY-INPUT-UNKNOWN module={RuleFixture.RingPath}",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains(
            $"reason=consumer-path-input-missing:{intermediatePath}",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.DoesNotContain(
            "UTILITY-CONSUMER-UNREACHABLE",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void MissingReportInputFailsClosedInsteadOfMeaningZeroEdges()
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] = WithUtility(
            fixture.Files[RuleFixture.RingPath],
            "kind=certified-instance; basis=consumer=D5/S0/Carrier/ValuesBinding.fixtureValue");
        fixture.Reports.Remove(RuleFixture.RingPath);

        var diagnostics = EvaluateFirstFreeze(fixture, validateLean: false);

        var diagnostic = Assert.Single(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Block);
        Assert.Contains(
            $"UTILITY-INPUT-UNKNOWN module={RuleFixture.RingPath}",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains("reason=current-lean-report-missing", diagnostic.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("UTILITY-CONSUMER-UNREACHABLE", diagnostic.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("instance", "D5/S0/Carrier/Ring.missing")]
    [InlineData("premises", "D5/S0/Carrier/Ring.goldenRing,D5/S0/Carrier/Ring.missing")]
    [InlineData("result", "D5/S0/Carrier/Ring.missing")]
    public void DanglingOptionalDeclarationIsBlocked(string key, string value)
    {
        var kind = key == "premises" ? "numeric-reduction" : "certified-instance";
        var diagnostic = Assert.Single(EvaluateFirstFreeze(
            $"kind={kind}; basis=refutes=gid:D5/S0/Carrier/Ring.goldenRing; {key}={value}"),
            item => item.AdmissionEffect is AdmissionEffect.Block);

        Assert.Contains(
            $"UTILITY-TARGET-DANGLING module={RuleFixture.RingPath}",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains("target=D5/S0/Carrier/Ring.missing", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RefutesTaskIsObservedNotBlocked()
    {
        var diagnostics = EvaluateTaskUtility(
            "kind=bounded-enumeration; basis=refutes=task:D5-T0098");

        AssertSoftObservation(
            diagnostics,
            "kind=bounded-enumeration basis=refutes target=task:D5-T0098");
    }

    [Fact]
    public void TerminalIsObservedNotBlocked()
    {
        var diagnostics = EvaluateTaskUtility(
            "kind=certified-instance; basis=terminal=task:D5-T0098");

        AssertSoftObservation(
            diagnostics,
            "kind=certified-instance basis=terminal target=task:D5-T0098");
    }

    [Fact]
    public void NoneIsObservedNotBlocked()
    {
        var diagnostics = EvaluateFirstFreeze("none");

        AssertSoftObservation(diagnostics, "kind=none basis=none target=none");
    }

    [Fact]
    public void RefutesAtomWithoutExactCoverageEdgeIsBlocked()
    {
        var fixture = AtomUtilityFixture(
            "sha256:0000000000000000000000000000000000000000000000000000000000000000");

        var diagnostic = Assert.Single(
            EvaluateFirstFreeze(fixture),
            item => item.AdmissionEffect is AdmissionEffect.Block);

        Assert.Contains(
            $"UTILITY-REFUTES-ATOM-NO-COVERAGE module={RuleFixture.RingPath}",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains($"atom={RuleFixture.FixtureAtomId}", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RefutesAtomWithNullTargetIsBlocked()
    {
        var fixture = AtomUtilityFixture(targetStatementId: null);

        var diagnostic = Assert.Single(
            EvaluateFirstFreeze(fixture),
            item => item.AdmissionEffect is AdmissionEffect.Block);

        Assert.Contains(
            $"UTILITY-REFUTES-ATOM-NO-COVERAGE module={RuleFixture.RingPath}",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void RefutesAtomWithExactCoverageEdgeIsObserved()
    {
        var fixture = new RuleFixture();
        var statementId = Assert.Single(CanonicalStatementWriter.DeclarationStatementIds(
            RepoPath.CreateKnown(RuleFixture.RingPath),
            fixture.Reports[RuleFixture.RingPath])).StatementId.Value;
        SetAtomUtility(fixture, statementId);

        var diagnostics = EvaluateFirstFreeze(fixture);

        AssertSoftObservation(
            diagnostics,
            $"kind=bounded-enumeration basis=refutes target=atom:{RuleFixture.FixtureAtomId}");
    }

    [Fact]
    public void ExistingFrozenSixLineHeaderIsOutsideDelta()
    {
        var fixture = new RuleFixture();
        var statePath = AddExistingFrozenState(fixture);

        var diagnostics = RuleCatalog.Default.EvaluateSingle(
            UtilityRuleId,
            fixture.Build(RawChangeSet.CreateWithKinds(
                [(statePath, RawChangeKind.Added)]))).Diagnostics;

        Assert.Empty(diagnostics);
    }

    [Fact]
    [BaseFactScopeProbe(30)]
    public void Sl030EvaluateScopesFirstFreezeDeltaAndKeepsImplementationWakeup()
    {
        var historical = new RuleFixture();
        AddExistingFrozenState(historical);
        Assert.Empty(RuleCatalog.Default.EvaluateSingle(
            UtilityRuleId,
            historical.Build(RawChangeSet.Create([RuleFixture.BlueprintPath]))).Diagnostics);

        var firstFreezeDiagnostic = Assert.Single(
            EvaluateFirstFreeze(utility: null),
            item => item.AdmissionEffect is AdmissionEffect.Block);
        Assert.Contains("UTILITY-MISSING", firstFreezeDiagnostic.Message, StringComparison.Ordinal);

        const string implementation =
            "tools/StrataLint.Engine/Rules/TheoryGeneration/UtilityAdmissionRule.cs";
        var implementationOnly = new RuleFixture();
        implementationOnly.Files[implementation] = "// candidate rule implementation\n";
        var implementationContext = implementationOnly.Build(RawChangeSet.Create([implementation]));
        Assert.True(UtilityAdmissionRule.IsAffectedBy(implementationContext));
        Assert.Empty(RuleCatalog.Default.EvaluateSingle(
            UtilityRuleId,
            implementationContext).Diagnostics);
    }

    [Fact]
    public void FrozenUtilityRatchetBlocksChange()
    {
        var fixture = new RuleFixture();
        AddExistingFrozenState(fixture);
        fixture.Baseline[RuleFixture.RingPath] = WithUtility(
            fixture.Baseline[RuleFixture.RingPath],
            "kind=certified-instance; basis=terminal=task:D5-T0001");
        fixture.Files[RuleFixture.RingPath] = WithUtility(
            fixture.Files[RuleFixture.RingPath],
            "none");

        var diagnostic = Assert.Single(RuleCatalog.Default.EvaluateSingle(
            UtilityRuleId,
            fixture.Build(RawChangeSet.Create([RuleFixture.RingPath]))).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(RuleFixture.RingPath, diagnostic.Path);
        Assert.Contains(
            $"UTILITY-RATCHET module={RuleFixture.RingPath}",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void MalformedAddedFrozenStatePathFailsClosed()
    {
        const string malformed = "Golden/Frozen/state/not-a-module.json";
        var fixture = new RuleFixture();
        fixture.Files[malformed] = "{}\n";

        var diagnostic = Assert.Single(RuleCatalog.Default.EvaluateSingle(
            UtilityRuleId,
            fixture.Build(RawChangeSet.CreateWithKinds(
                [(malformed, RawChangeKind.Added)]))).Diagnostics);

        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(malformed, diagnostic.Path);
        Assert.Contains(
            $"UTILITY-INPUT-UNKNOWN module={malformed} reason=invalid-frozen-state-path",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void MalformedStateAndLeanAddedTogetherYieldNamedUnknownNotInfrastructureFailure()
    {
        const string malformedModule = "D5/s0/Carrier/Bad.lean";
        const string malformedState =
            "Golden/Frozen/state/D5/s0/Carrier/Bad.lean.json";
        var fixture = new RuleFixture();
        fixture.Files[malformedModule] = fixture.Files[RuleFixture.RingPath].Replace(
            "D5/S0/Carrier/Ring",
            "D5/s0/Carrier/Bad",
            StringComparison.Ordinal);
        fixture.Reports[malformedModule] = fixture.Reports[RuleFixture.RingPath];
        fixture.Files[malformedState] = "{}\n";
        var changes = RawChangeSet.CreateWithKinds(
        [
            (malformedModule, RawChangeKind.Added),
            (malformedState, RawChangeKind.Added),
        ]);

        var outcome = RuleCatalog.Default.Execute(
            fixture.BuildForRuleCompatibility(changes));

        if (outcome is RuleExecutionOutcome.InfrastructureFailure failure)
        {
            Assert.Fail(failure.Message);
        }

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(outcome);
        Assert.Contains(
            completed.Capability.Diagnostics,
            diagnostic => diagnostic.RuleId == UtilityRuleId
                && diagnostic.AdmissionEffect is AdmissionEffect.Block
                && diagnostic.Path == malformedState
                && diagnostic.Message.Contains(
                    $"UTILITY-INPUT-UNKNOWN module={malformedState} "
                    + "reason=invalid-frozen-state-path",
                    StringComparison.Ordinal));
    }

    [Fact]
    public void DuplicateAtomTargetIsInputUnknownNotInfrastructureFailure()
    {
        var fixture = AtomUtilityFixture(targetStatementId: null);
        fixture.Files[RuleFixture.FixtureBackfillAtomPath.Replace(
            "/partial-open/",
            "/residual-open/",
            StringComparison.Ordinal)] = fixture.Files[RuleFixture.FixtureBackfillAtomPath];
        var statePath = FrozenStatePath.FromModulePath(
            RepoPath.CreateKnown(RuleFixture.RingPath)).Value;
        fixture.Files[statePath] =
            "{\"statement_id\":\"sha256:0000000000000000000000000000000000000000000000000000000000000000\"}\n";

        var outcome = RuleCatalog.Default.Execute(fixture.Build(
            RawChangeSet.CreateWithKinds([(statePath, RawChangeKind.Added)])));

        if (outcome is RuleExecutionOutcome.InfrastructureFailure failure)
        {
            Assert.Fail(failure.Message);
        }

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(outcome);
        Assert.Contains(
            completed.Capability.Diagnostics,
            diagnostic => diagnostic.RuleId == UtilityRuleId
                && diagnostic.AdmissionEffect is AdmissionEffect.Block
                && diagnostic.Message == $"UTILITY-INPUT-UNKNOWN module={RuleFixture.RingPath} "
                    + $"reason=ambiguous-atom-target:{RuleFixture.FixtureAtomId}");
    }

    [Fact]
    public void AmbiguousAtomModuleStillEmitsObserveAndDoesNotStopLaterFirstFreezeModules()
    {
        var fixture = AtomUtilityFixture(targetStatementId: null);
        fixture.Files[RuleFixture.FixtureBackfillAtomPath.Replace(
            "/partial-open/",
            "/residual-open/",
            StringComparison.Ordinal)] = fixture.Files[RuleFixture.FixtureBackfillAtomPath];
        fixture.Files[RuleFixture.ValuesBindingPath] = WithUtility(
            fixture.Files[RuleFixture.ValuesBindingPath],
            "none");
        var ringStatePath = FrozenStatePath.FromModulePath(
            RepoPath.CreateKnown(RuleFixture.RingPath)).Value;
        var valuesStatePath = FrozenStatePath.FromModulePath(
            RepoPath.CreateKnown(RuleFixture.ValuesBindingPath)).Value;
        const string state =
            "{\"statement_id\":\"sha256:0000000000000000000000000000000000000000000000000000000000000000\"}\n";
        fixture.Files[ringStatePath] = state;
        fixture.Files[valuesStatePath] = state;

        var outcome = RuleCatalog.Default.Execute(fixture.Build(
            RawChangeSet.CreateWithKinds(
            [
                (ringStatePath, RawChangeKind.Added),
                (valuesStatePath, RawChangeKind.Added),
            ])));

        if (outcome is RuleExecutionOutcome.InfrastructureFailure failure)
        {
            Assert.Fail(failure.Message);
        }

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(outcome);
        var utilityDiagnostics = completed.Capability.Diagnostics
            .Where(diagnostic => diagnostic.RuleId == UtilityRuleId)
            .ToArray();
        Assert.Contains(
            utilityDiagnostics,
            diagnostic => diagnostic.AdmissionEffect is AdmissionEffect.Block
                && diagnostic.Path == RuleFixture.RingPath
                && diagnostic.Message == $"UTILITY-INPUT-UNKNOWN module={RuleFixture.RingPath} "
                    + $"reason=ambiguous-atom-target:{RuleFixture.FixtureAtomId}");
        var ambiguousObservation = Assert.Single(
            utilityDiagnostics,
            diagnostic => diagnostic.AdmissionEffect is AdmissionEffect.Observe
                && diagnostic.Path == RuleFixture.RingPath);
        Assert.Equal(
            $"UTILITY-OBSERVED module={RuleFixture.RingPath} "
            + $"kind=bounded-enumeration basis=refutes target=atom:{RuleFixture.FixtureAtomId} "
            + "semantics=unverified-by-machine",
            ambiguousObservation.Message);
        Assert.Contains(
            utilityDiagnostics,
            diagnostic => diagnostic.AdmissionEffect is AdmissionEffect.Observe
                && diagnostic.Path == RuleFixture.ValuesBindingPath
                && diagnostic.Message == $"UTILITY-OBSERVED module={RuleFixture.ValuesBindingPath} "
                    + "kind=none basis=none target=none semantics=unverified-by-machine");
        Assert.DoesNotContain(
            utilityDiagnostics,
            diagnostic => diagnostic.AdmissionEffect is AdmissionEffect.Block
                && diagnostic.Path == RuleFixture.ValuesBindingPath);
    }

    [Fact]
    public void LegacySixLineHeaderStillParses()
    {
        var fixture = new RuleFixture();

        Assert.True(RepositoryRules.TryHeader(
            fixture.Files[RuleFixture.RingPath],
            out var header));
        Assert.Null(header.Utility);
    }

    [Fact]
    public void SevenLineHeaderCapturesUtility()
    {
        var fixture = new RuleFixture();
        const string utility = "kind=certified-instance; basis=terminal=task:D5-T0001";

        Assert.True(RepositoryRules.TryHeader(
            WithUtility(fixture.Files[RuleFixture.RingPath], utility),
            out var header));
        Assert.Equal(utility, header.Utility);
    }

    [Fact]
    public void HeaderUtilityLineRequiresSpaceAfterColonAcrossEntries()
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath].Replace(
            "   anchors: []\n",
            "   anchors: []\n   utility:none\n",
            StringComparison.Ordinal);

        Assert.False(RepositoryRules.TryHeader(
            fixture.Files[RuleFixture.RingPath],
            out _));

        var diagnostic = Assert.Single(RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(12),
            fixture.Build(RawChangeSet.Create([RuleFixture.RingPath]))).Diagnostics);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(RuleFixture.RingPath, diagnostic.Path);
    }

    [Fact]
    public void BodyOnlyLeanEditDoesNotWakeUtilityRule()
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] += "-- body-only change\n";
        var context = fixture.Build(RawChangeSet.Create([RuleFixture.RingPath]));

        Assert.False(UtilityAdmissionRule.IsAffectedBy(context));
    }

    [Fact]
    public void RuleImplementationChangeWakesWithoutExpandingFirstFreezeSet()
    {
        const string implementation =
            "tools/StrataLint.Engine/Rules/TheoryGeneration/UtilityAdmissionRule.cs";
        var fixture = new RuleFixture();
        fixture.Files[implementation] = "// candidate rule implementation\n";
        var context = fixture.Build(RawChangeSet.Create([implementation]));

        Assert.True(UtilityAdmissionRule.IsAffectedBy(context));
        Assert.Empty(RuleCatalog.Default.EvaluateSingle(UtilityRuleId, context).Diagnostics);
    }

    [Theory]
    [InlineData("atom:0000000000000000000000000000000000000000000000000000000000000000")]
    [InlineData("task:D5-T0099")]
    public void DanglingSoftTargetIsBlocked(string target)
    {
        var diagnostic = Assert.Single(EvaluateFirstFreeze(
            $"kind=bounded-enumeration; basis=terminal={target}"),
            item => item.AdmissionEffect is AdmissionEffect.Block);

        Assert.Contains(
            $"UTILITY-TARGET-DANGLING module={RuleFixture.RingPath} target={target}",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void MalformedBackfillFailsClosed()
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.FixtureBackfillAtomPath] = "not: canonical\n";
        fixture.Files[RuleFixture.RingPath] = WithUtility(
            fixture.Files[RuleFixture.RingPath],
            $"kind=bounded-enumeration; basis=terminal=atom:{RuleFixture.FixtureAtomId}");

        var diagnostic = Assert.Single(
            EvaluateFirstFreeze(fixture),
            item => item.AdmissionEffect is AdmissionEffect.Block);

        Assert.Contains(
            $"UTILITY-INPUT-UNKNOWN module={RuleFixture.RingPath} reason=backfill-load-failed",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void RefutesGidIsObservedNotBlocked()
    {
        var diagnostics = EvaluateFirstFreeze(
            "kind=bounded-enumeration; basis=refutes=gid:D5/S0/Carrier/Ring.goldenRing");

        AssertSoftObservation(
            diagnostics,
            "kind=bounded-enumeration basis=refutes "
            + "target=gid:D5/S0/Carrier/Ring.goldenRing");
    }

    private static IReadOnlyList<Diagnostic> EvaluateFirstFreeze(string? utility)
    {
        var fixture = new RuleFixture();
        if (utility is not null)
        {
            fixture.Files[RuleFixture.RingPath] = WithUtility(
                fixture.Files[RuleFixture.RingPath],
                utility);
        }

        return EvaluateFirstFreeze(fixture);
    }

    private static IReadOnlyList<Diagnostic> EvaluateTaskUtility(string utility)
    {
        var fixture = new RuleFixture();
        fixture.AddSyntheticUnregisteredFrontierTask("D5-T0098");
        fixture.Files[RuleFixture.RingPath] = WithUtility(
            fixture.Files[RuleFixture.RingPath],
            utility);
        return EvaluateFirstFreeze(fixture);
    }

    private static RuleFixture AtomUtilityFixture(string? targetStatementId)
    {
        var fixture = new RuleFixture();
        SetAtomUtility(fixture, targetStatementId);
        return fixture;
    }

    private static void SetAtomUtility(RuleFixture fixture, string? targetStatementId)
    {
        fixture.Files[RuleFixture.RingPath] = WithUtility(
            fixture.Files[RuleFixture.RingPath],
            $"kind=bounded-enumeration; basis=refutes=atom:{RuleFixture.FixtureAtomId}");
        fixture.Files[RuleFixture.FixtureBackfillAtomPath] =
            fixture.Files[RuleFixture.FixtureBackfillAtomPath]
                .Replace(
                    "gid: D5/S0/Carrier/BackfillTarget",
                    "gid: D5/S0/Carrier/Ring.goldenRing",
                    StringComparison.Ordinal)
                .Replace(
                    "target_statement_id: null",
                    $"target_statement_id: {targetStatementId ?? "null"}",
                    StringComparison.Ordinal);
    }

    private static string AddExistingFrozenState(RuleFixture fixture)
    {
        var statePath = FrozenStatePath.FromModulePath(
            RepoPath.CreateKnown(RuleFixture.RingPath)).Value;
        const string state =
            "{\"statement_id\":\"sha256:0000000000000000000000000000000000000000000000000000000000000000\"}\n";
        fixture.Files[statePath] = state;
        fixture.Baseline[statePath] = state;
        return statePath;
    }

    private static IReadOnlyList<Diagnostic> EvaluateFirstFreeze(
        RuleFixture fixture,
        bool validateLean = true)
    {
        var statePath = FrozenStatePath.FromModulePath(
            RepoPath.CreateKnown(RuleFixture.RingPath)).Value;
        fixture.Files[statePath] =
            "{\"statement_id\":\"sha256:0000000000000000000000000000000000000000000000000000000000000000\"}\n";
        var changes = RawChangeSet.CreateWithKinds([(statePath, RawChangeKind.Added)]);
        var context = validateLean
            ? fixture.Build(changes)
            : fixture.BuildForRuleCompatibility(changes);
        return RuleCatalog.Default.EvaluateSingle(UtilityRuleId, context).Diagnostics;
    }

    private static string WithUtility(string text, string utility) =>
        text.Replace(
            "   anchors: []\n",
            $"   anchors: []\n   utility: {utility}\n",
            StringComparison.Ordinal);

    private static void AssertSoftObservation(
        IReadOnlyList<Diagnostic> diagnostics,
        string fields)
    {
        Assert.DoesNotContain(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Block);
        var observation = Assert.Single(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Observe);
        Assert.Equal(RuleFixture.RingPath, observation.Path);
        Assert.Equal(
            $"UTILITY-OBSERVED module={RuleFixture.RingPath} {fields} "
            + "semantics=unverified-by-machine",
            observation.Message);
    }

    private static void AssertBlockedObservationPair(
        IReadOnlyList<Diagnostic> diagnostics,
        string blockCode,
        string observationFields)
    {
        var block = Assert.Single(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Block);
        Assert.Contains(blockCode, block.Message, StringComparison.Ordinal);
        var observation = Assert.Single(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Observe);
        Assert.Equal(
            $"UTILITY-OBSERVED module={RuleFixture.RingPath} {observationFields} "
            + "semantics=unverified-by-machine",
            observation.Message);
    }
}
