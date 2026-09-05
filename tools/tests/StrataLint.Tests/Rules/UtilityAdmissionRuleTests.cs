using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class UtilityAdmissionRuleTests
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
