using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class UtilityAdmissionTestSupport
{
    internal static readonly RuleId UtilityRuleId = RuleId.CreateKnown(31);

    internal static IReadOnlyList<Diagnostic> EvaluateFirstFreeze(string? utility)
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

    internal static IReadOnlyList<Diagnostic> EvaluateTaskUtility(string utility, bool refutation = false)
    {
        var fixture = new RuleFixture();
        fixture.AddSyntheticUnregisteredFrontierTask("D5-T0098");
        if (refutation) utility = AddRefutationEvidence(fixture, utility);
        fixture.Files[RuleFixture.RingPath] = WithUtility(
            fixture.Files[RuleFixture.RingPath],
            utility);
        return EvaluateFirstFreeze(fixture);
    }

    internal static RuleFixture AtomUtilityFixture(string? targetStatementId)
    {
        var fixture = new RuleFixture();
        SetAtomUtility(fixture, targetStatementId);
        return fixture;
    }

    internal static void SetAtomUtility(RuleFixture fixture, string? targetStatementId)
    {
        fixture.Files[RuleFixture.RingPath] = WithUtility(
            fixture.Files[RuleFixture.RingPath],
            AddRefutationEvidence(fixture,
                $"kind=bounded-enumeration; basis=refutes=atom:{RuleFixture.FixtureAtomId}"));
        fixture.Files[RuleFixture.FixtureBackfillAtomPath] =
            fixture.Files[RuleFixture.FixtureBackfillAtomPath]
                .Replace(
                    "gid: D5/S0/Carrier/BackfillTarget",
                    "gid: " + UtilityRefutationTests.Result,
                    StringComparison.Ordinal)
                .Replace(
                    "target_statement_id: null",
                    $"target_statement_id: {targetStatementId ?? "null"}",
                    StringComparison.Ordinal);
    }

    internal static string AddRefutationEvidence(RuleFixture fixture, string utility)
    {
        fixture.Reports[RuleFixture.RingPath] = fixture.Reports[RuleFixture.RingPath] with
        {
            Declarations = fixture.Reports[RuleFixture.RingPath].Declarations.AddRange(new LeanDeclaration[] {
                new LeanDeclaration("proposed_law", "def", "Prop := False", []),
                new LeanDeclaration("refuted_law", "theorem", "Not proposed_law", []),
            }),
            Refutation = new(UtilityRefutationTests.Claim, UtilityRefutationTests.Result, true),
        };
        return utility + "; result=" + UtilityRefutationTests.Result + "; claim=" + UtilityRefutationTests.Claim;
    }

    internal static string AddExistingFrozenState(RuleFixture fixture)
    {
        var statePath = FrozenStatePath.FromModulePath(
            RepoPath.CreateKnown(RuleFixture.RingPath)).Value;
        const string state =
            "{\"statement_id\":\"sha256:0000000000000000000000000000000000000000000000000000000000000000\"}\n";
        fixture.Files[statePath] = state;
        fixture.Baseline[statePath] = state;
        return statePath;
    }

    internal static IReadOnlyList<Diagnostic> EvaluateFirstFreeze(
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

    internal static string WithUtility(string text, string utility) =>
        text.Replace(
            "   anchors: []\n",
            $"   anchors: []\n   utility: {utility}\n",
            StringComparison.Ordinal);

    internal static void AssertSoftObservation(
        IReadOnlyList<Diagnostic> diagnostics,
        string fields)
    {
        Assert.DoesNotContain(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Block);
        var observation = Assert.Single(
            diagnostics,
            item => item.AdmissionEffect is AdmissionEffect.Observe
                && item.Message.StartsWith("UTILITY-OBSERVED ", StringComparison.Ordinal));
        Assert.Equal(RuleFixture.RingPath, observation.Path);
        Assert.Equal(
            $"UTILITY-OBSERVED module={RuleFixture.RingPath} {fields} "
            + "semantics=unverified-by-machine",
            observation.Message);
    }

    internal static void AssertBlockedObservationPair(
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
            item => item.AdmissionEffect is AdmissionEffect.Observe
                && item.Message.StartsWith("UTILITY-OBSERVED ", StringComparison.Ordinal));
        Assert.Equal(
            $"UTILITY-OBSERVED module={RuleFixture.RingPath} {observationFields} "
            + "semantics=unverified-by-machine",
            observation.Message);
    }
}
