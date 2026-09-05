using StrataLint.Engine;
using static StrataLint.Tests.UtilityAdmissionTestSupport;

namespace StrataLint.Tests;

public sealed class UtilityAdmissionObservationTests
{
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
            UtilityAdmissionTestSupport.UtilityRuleId,
            fixture.Build(RawChangeSet.CreateWithKinds(
                [(statePath, RawChangeKind.Added)]))).Diagnostics;

        Assert.Empty(diagnostics);
    }

    [Fact]
    [BaseFactScopeProbe(31)]
    public void Sl031EvaluateScopesFirstFreezeDeltaAndKeepsImplementationWakeup()
    {
        var historical = new RuleFixture();
        AddExistingFrozenState(historical);
        Assert.Empty(RuleCatalog.Default.EvaluateSingle(
            UtilityAdmissionTestSupport.UtilityRuleId,
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
            UtilityAdmissionTestSupport.UtilityRuleId,
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
            UtilityAdmissionTestSupport.UtilityRuleId,
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
            UtilityAdmissionTestSupport.UtilityRuleId,
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
            diagnostic => diagnostic.RuleId == UtilityAdmissionTestSupport.UtilityRuleId
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
            diagnostic => diagnostic.RuleId == UtilityAdmissionTestSupport.UtilityRuleId
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
            .Where(diagnostic => diagnostic.RuleId == UtilityAdmissionTestSupport.UtilityRuleId)
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
}
