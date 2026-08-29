using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MissionFileLoaderTests
{
    private const string FrontierEligibilityJson = """
          "frontier_eligibility": [
            {
              "source_ref": "D5/X_Frontier/GovernanceTicket",
              "kind": "governance"
            }
          ],

        """;

    private const string RetiredFrontierEligibilityJson = """
          "frontier_eligibility": [
            {
              "source_ref": "D5/X_Frontier/GovernanceTicket",
              "kind": "retired",
              "delivery_gids": [
                "D5/X_Frontier/GovernanceTicket.fixture_delivery"
              ]
            }
          ],

        """;

    [Fact]
    public void BaselineMissionWithoutFrontierEligibilityRemainsLoadable()
    {
        var baselineMission = ValidMission.Replace(
            FrontierEligibilityJson,
            string.Empty,
            StringComparison.Ordinal);

        var loaded = Assert.IsType<MissionLoadOutcome.Loaded>(
            MissionFileLoader.Load(Snapshot(baselineMission)));

        Assert.Empty(loaded.Policy.FrontierEligibility);
    }

    [Fact]
    public void FrontierEligibilityIsTypedAndCanonical()
    {
        var loaded = Assert.IsType<MissionLoadOutcome.Loaded>(
            MissionFileLoader.Load(Snapshot(ValidMission)));

        var entry = Assert.Single(loaded.Policy.FrontierEligibility);
        Assert.Equal("D5/X_Frontier/GovernanceTicket", entry.SourceRef);
        Assert.Equal(FrontierEligibilityKind.Governance, entry.Kind);
        using var canonical = JsonDocument.Parse(MissionFileLoader.CanonicalBytes(loaded.Policy));
        Assert.Equal(
            "governance",
            canonical.RootElement
                .GetProperty("frontier_eligibility")[0]
                .GetProperty("kind")
                .GetString());
    }

    [Fact]
    public void RetiredFrontierEligibilityCarriesCanonicalDeliveryEvidence()
    {
        var mission = ValidMission.Replace(
            FrontierEligibilityJson,
            RetiredFrontierEligibilityJson,
            StringComparison.Ordinal);

        var loaded = Assert.IsType<MissionLoadOutcome.Loaded>(
            MissionFileLoader.Load(Snapshot(mission)));
        var entry = Assert.Single(loaded.Policy.FrontierEligibility);

        Assert.Equal(FrontierEligibilityKind.Retired, entry.Kind);
        Assert.Single(entry.DeliveryGids);
        Assert.Equal(
            "D5/X_Frontier/GovernanceTicket.fixture_delivery",
            entry.DeliveryGids[0]);
        using var canonical = JsonDocument.Parse(MissionFileLoader.CanonicalBytes(loaded.Policy));
        Assert.Equal(
            "D5/X_Frontier/GovernanceTicket.fixture_delivery",
            canonical.RootElement
                .GetProperty("frontier_eligibility")[0]
                .GetProperty("delivery_gids")[0]
                .GetString());
    }

    [Fact]
    public void RetiredFrontierEligibilityRejectsEmptyDeliveryEvidence()
    {
        var mission = ValidMission.Replace(
            FrontierEligibilityJson,
            RetiredFrontierEligibilityJson.Replace(
                "\"D5/X_Frontier/GovernanceTicket.fixture_delivery\"",
                string.Empty,
                StringComparison.Ordinal),
            StringComparison.Ordinal);

        var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
            MissionFileLoader.Load(Snapshot(mission)));

        Assert.Equal(MissionLoadErrorCode.InvalidSchema, invalid.Error.Code);
        Assert.Contains(
            "must contain canonical formal declaration GIDs",
            invalid.Error.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void RetiredFrontierEligibilityRejectsDanglingDeliveryEvidence()
    {
        var mission = ValidMission.Replace(
            FrontierEligibilityJson,
            RetiredFrontierEligibilityJson.Replace(
                "D5/X_Frontier/GovernanceTicket.fixture_delivery",
                "D5/S0/Carrier/Ring.missing_delivery",
                StringComparison.Ordinal),
            StringComparison.Ordinal);

        var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
            MissionFileLoader.Load(Snapshot(mission)));

        Assert.Equal(MissionLoadErrorCode.InvalidSchema, invalid.Error.Code);
        Assert.Contains(
            "delivery target is missing or noncanonical",
            invalid.Error.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void FrontierEligibilityRejectsUnknownKeysKindsDuplicatesAndDanglingSources()
    {
        var unknownKey = ValidMission.Replace(
            "\"kind\": \"governance\"",
            "\"kind\": \"governance\", \"unknown\": true",
            StringComparison.Ordinal);
        var unknownKind = ValidMission.Replace(
            "\"kind\": \"governance\"",
            "\"kind\": \"mathematics\"",
            StringComparison.Ordinal);
        var duplicate = ValidMission.Replace(
            "\"kind\": \"governance\"",
            "\"kind\": \"governance\"\n"
            + "    },\n"
            + "    {\n"
            + "      \"source_ref\": \"D5/X_Frontier/GovernanceTicket\",\n"
            + "      \"kind\": \"governance\"",
            StringComparison.Ordinal);
        var dangling = ValidMission.Replace(
            "D5/X_Frontier/GovernanceTicket",
            "D5/X_Frontier/Missing",
            StringComparison.Ordinal);

        AssertInvalid(unknownKey, "frontier_eligibility[0]");
        AssertInvalid(unknownKind, "frontier_eligibility[0].kind");
        AssertInvalid(duplicate, "source_ref values must be unique");
        AssertInvalid(dangling, "target is missing");

        static void AssertInvalid(string mission, string message)
        {
            var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
                MissionFileLoader.Load(Snapshot(mission)));
            Assert.Equal(MissionLoadErrorCode.InvalidSchema, invalid.Error.Code);
            Assert.Contains(message, invalid.Error.Message, StringComparison.Ordinal);
        }
    }
}
