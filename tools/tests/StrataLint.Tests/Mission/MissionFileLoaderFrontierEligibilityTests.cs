using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MissionFileLoaderTests
{
    private const string FrontierEligibilityJson = """
          "frontier_eligibility": [
            {
              "source_ref": "D5/X_Frontier/GovernanceDeferrals",
              "kind": "governance"
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
        Assert.Equal("D5/X_Frontier/GovernanceDeferrals", entry.SourceRef);
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
            + "      \"source_ref\": \"D5/X_Frontier/GovernanceDeferrals\",\n"
            + "      \"kind\": \"governance\"",
            StringComparison.Ordinal);
        var dangling = ValidMission.Replace(
            "D5/X_Frontier/GovernanceDeferrals",
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
