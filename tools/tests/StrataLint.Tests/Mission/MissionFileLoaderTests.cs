using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class MissionFileLoaderTests
{
    private const string TicketIndex = """
        D5-T0039 = "D5/X_Frontier/GovernanceDeferrals"
        D5-T0040 = "D5/X_Frontier/GovernanceDeferrals"
        D5-T0041 = "D5/X_Frontier/GovernanceDeferrals"
        D5-T0042 = "D5/X_Frontier/GovernanceDeferrals"
        """;

    private const string GovernanceDeferrals = """
        /-- TASK D5-T0039 | difficulty:3 -/
        def missionNoveltyMeasurementTicket : Unit := ()
        /-- TASK D5-T0040 | difficulty:3 -/
        def missionDependencyReadinessMeasurementTicket : Unit := ()
        /-- TASK D5-T0041 | difficulty:3 -/
        def missionStructuralRealizationMeasurementTicket : Unit := ()
        /-- TASK D5-T0042 | difficulty:3 -/
        def missionReceiptPotentialMeasurementTicket : Unit := ()
        """;

    private static readonly string ValidMission = """
        # Mission

        ```mission-v1
        {
          "schema": "trureturing-mission-v1",
          "north_star": {
            "target": "two hearts",
            "policy": "aspirational-not-direct"
          },
          "value_order": [
            "understanding-over-quantity",
            "honesty-over-speed",
            "negative-knowledge-equals-positive-results"
          ],
          "worth_vector": {
            "novelty": { "state": "open", "case_id": "D5-T0039" },
            "dependency_readiness": { "state": "open", "case_id": "D5-T0040" },
            "structural_realization": { "state": "open", "case_id": "D5-T0041" },
            "receipt_potential": { "state": "open", "case_id": "D5-T0042" }
          },
          "selection": {
            "order_kind": "bootstrap eligibility order",
            "tie_break": "canonical candidate id"
          },
          "prohibitions": [
            "sorry-count optimization",
            "trivial-lemma accumulation",
            "citation chasing"
          ]
        }
        ```
        """ + "\n";

    [Fact]
    public void MissingMissionReturnsTypedFailClosedError()
    {
        var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
            MissionFileLoader.Load(Snapshot(mission: null)));

        Assert.Equal(MissionLoadErrorCode.Missing, invalid.Error.Code);
    }

    [Fact]
    public void MalformedMissionReturnsTypedFailClosedError()
    {
        var malformed = ValidMission.Replace(
            "\"schema\": \"trureturing-mission-v1\"",
            "\"schema\" \"trureturing-mission-v1\"",
            StringComparison.Ordinal);

        var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
            MissionFileLoader.Load(Snapshot(malformed)));

        Assert.Equal(MissionLoadErrorCode.InvalidFormat, invalid.Error.Code);
    }

    [Fact]
    public void UnknownFactorCannotBeSilentlyFilledWithANumericDefault()
    {
        var unknownFactor = ValidMission.Replace(
            "\"novelty\": { \"state\": \"open\", \"case_id\": \"D5-T0039\" }",
            "\"unknown\": { \"state\": \"measured\", \"value\": 1, \"receipt_ref\": \"receipt:invented\" }",
            StringComparison.Ordinal);

        var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
            MissionFileLoader.Load(Snapshot(unknownFactor)));

        Assert.Equal(MissionLoadErrorCode.InvalidWorthVector, invalid.Error.Code);
    }

    [Fact]
    public void OpenFactorCannotCarryASilentNumericDefault()
    {
        var defaulted = ValidMission.Replace(
            "{ \"state\": \"open\", \"case_id\": \"D5-T0039\" }",
            "{ \"state\": \"open\", \"case_id\": \"D5-T0039\", \"value\": 1 }",
            StringComparison.Ordinal);

        var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
            MissionFileLoader.Load(Snapshot(defaulted)));

        Assert.Equal(MissionLoadErrorCode.InvalidWorthState, invalid.Error.Code);
    }

    [Fact]
    public void DanglingOpenCaseIdIsRejected()
    {
        var dangling = ValidMission.Replace("D5-T0039", "D5-T9999", StringComparison.Ordinal);

        var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
            MissionFileLoader.Load(Snapshot(dangling)));

        Assert.Equal(MissionLoadErrorCode.DanglingCaseReference, invalid.Error.Code);
    }

    [Fact]
    public void ReplayProducesByteIdenticalParsedContractAndDerivedOrder()
    {
        var snapshot = Snapshot(ValidMission);
        var first = Assert.IsType<MissionLoadOutcome.Loaded>(MissionFileLoader.Load(snapshot));
        var second = Assert.IsType<MissionLoadOutcome.Loaded>(MissionFileLoader.Load(snapshot));

        Assert.Equal(
            MissionFileLoader.CanonicalBytes(first.Policy),
            MissionFileLoader.CanonicalBytes(second.Policy));
        Assert.Equal(
            new[]
            {
                WorthFactorId.Novelty,
                WorthFactorId.DependencyReadiness,
                WorthFactorId.StructuralRealization,
                WorthFactorId.ReceiptPotential,
            },
            first.Policy.WorthVector.Factors.Select(static factor => factor.Id));
        Assert.Equal(
            WorthSelectionOrder.BootstrapEligibilityOrder,
            first.Policy.Selection.OrderKind);
    }

    [Fact]
    public void AllOpenFactorsRejectCompleteWorthArgmaxLabel()
    {
        var falseComplete = ValidMission.Replace(
            "bootstrap eligibility order",
            "complete worth argmax",
            StringComparison.Ordinal);

        var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
            MissionFileLoader.Load(Snapshot(falseComplete)));

        Assert.Equal(MissionLoadErrorCode.InvalidSelection, invalid.Error.Code);
    }

    [Fact]
    public void RepositoryMissionLoadsFourRegisteredOpenFactors()
    {
        var root = TestRepositoryLayout.FindRoot();
        var loaded = Assert.IsType<MissionLoadOutcome.Loaded>(
            MissionFileLoader.LoadRepository(root));

        Assert.Equal(4, loaded.Policy.WorthVector.Factors.Length);
        Assert.All(
            loaded.Policy.WorthVector.Factors,
            factor => Assert.IsType<WorthFactorState.Open>(factor.State));
    }

    private static RepositorySnapshot Snapshot(string? mission)
    {
        var entries = new List<RawRepositoryEntry>
        {
            RawRepositoryEntry.FromText(BackfillInventoryLoader.TicketIndexPath, TicketIndex),
            RawRepositoryEntry.FromText(
                "D5/X_Frontier/GovernanceDeferrals.lean",
                GovernanceDeferrals),
        };
        if (mission is not null)
        {
            entries.Add(RawRepositoryEntry.FromText(MissionFileLoader.RelativePath, mission));
        }

        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries))).Snapshot;
    }
}
