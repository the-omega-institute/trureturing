using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class MissionFileLoaderTests
{
    private const string TicketIndex = """
        D5-T0040 = "D5/X_Frontier/GovernanceDeferrals"
        D5-T0041 = "D5/X_Frontier/GovernanceDeferrals"
        D5-T0042 = "D5/X_Frontier/GovernanceDeferrals"
        D5-T0043 = "D5/X_Frontier/GovernanceDeferrals"
        """;

    private const string NoveltyTaskBlock = """
        /-- TASK D5-T0040
            The novelty factor's machine-replayable measurement receipt contract is not installed. Until it lands, docs/MISSION.md must remain open(D5-T0040) and must not claim a complete worth score. -/
        def missionNoveltyMeasurementTicket : Unit := ()
        """;

    private static readonly string GovernanceDeferrals = NoveltyTaskBlock + "\n" + """
        /-- TASK D5-T0041
            The dependency-readiness factor's machine-replayable measurement receipt contract is not installed. Until it lands, docs/MISSION.md must remain open(D5-T0041) and must not claim a complete worth score. -/
        def missionDependencyReadinessMeasurementTicket : Unit := ()
        /-- TASK D5-T0042
            The structural-realization factor's machine-replayable measurement receipt contract is not installed. Until it lands, docs/MISSION.md must remain open(D5-T0042) and must not claim a complete worth score. -/
        def missionStructuralRealizationMeasurementTicket : Unit := ()
        /-- TASK D5-T0043
            The receipt-potential factor's machine-replayable measurement receipt contract is not installed. Until it lands, docs/MISSION.md must remain open(D5-T0043) and must not claim a complete worth score. -/
        def missionReceiptPotentialMeasurementTicket : Unit := ()
        """ + "\n";

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
            "novelty": { "state": "open", "case_id": "D5-T0040" },
            "dependency_readiness": { "state": "open", "case_id": "D5-T0041" },
            "structural_realization": { "state": "open", "case_id": "D5-T0042" },
            "receipt_potential": { "state": "open", "case_id": "D5-T0043" }
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
            "\"novelty\": { \"state\": \"open\", \"case_id\": \"D5-T0040\" }",
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
            "{ \"state\": \"open\", \"case_id\": \"D5-T0040\" }",
            "{ \"state\": \"open\", \"case_id\": \"D5-T0040\", \"value\": 1 }",
            StringComparison.Ordinal);

        var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
            MissionFileLoader.Load(Snapshot(defaulted)));

        Assert.Equal(MissionLoadErrorCode.InvalidWorthState, invalid.Error.Code);
    }

    [Fact]
    public void DanglingOpenCaseIdIsRejected()
    {
        var dangling = ValidMission.Replace("D5-T0040", "D5-T9999", StringComparison.Ordinal);

        var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
            MissionFileLoader.Load(Snapshot(dangling)));

        Assert.Equal(MissionLoadErrorCode.DanglingCaseReference, invalid.Error.Code);
    }

    [Fact]
    public void NonBlockTaskMarkerCannotSatisfyAnOpenCaseReference()
    {
        var target = ReplaceNoveltyTaskBlock(
            "def staleMissionMarker : String := \"TASK D5-T0040\"");

        var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
            LoadRepository(Encoding.UTF8.GetBytes(ValidMission), target));

        Assert.Equal(MissionLoadErrorCode.DanglingCaseReference, invalid.Error.Code);
        Assert.Contains("D5-T0040", invalid.Error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ProseTaskMarkerCannotSatisfyAnOpenCaseReference()
    {
        var target = ReplaceNoveltyTaskBlock("""
            /-- This prose mentions TASK D5-T0040 but does not begin with it. -/
            def missionNoveltyMeasurementTicket : Unit := ()
            """);

        var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
            LoadRepository(Encoding.UTF8.GetBytes(ValidMission), target));

        Assert.Equal(MissionLoadErrorCode.DanglingCaseReference, invalid.Error.Code);
        Assert.Contains("D5-T0040", invalid.Error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void NonDocumentationCommentTaskMarkerCannotSatisfyAnOpenCaseReference()
    {
        var target = ReplaceNoveltyTaskBlock("""
            /- TASK D5-T0040
               This is a regular block comment, not a documentation-comment TASK block. -/
            def missionNoveltyMeasurementTicket : Unit := ()
            """);

        var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
            LoadRepository(Encoding.UTF8.GetBytes(ValidMission), target));

        Assert.Equal(MissionLoadErrorCode.DanglingCaseReference, invalid.Error.Code);
        Assert.Contains("D5-T0040", invalid.Error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DuplicateCanonicalTaskBlocksCannotSatisfyAnOpenCaseReference()
    {
        var target = ReplaceNoveltyTaskBlock(NoveltyTaskBlock + "\n" + NoveltyTaskBlock);

        var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
            LoadRepository(Encoding.UTF8.GetBytes(ValidMission), target));

        Assert.Equal(MissionLoadErrorCode.DanglingCaseReference, invalid.Error.Code);
        Assert.Contains("D5-T0040", invalid.Error.Message, StringComparison.Ordinal);
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
        using var canonical = JsonDocument.Parse(MissionFileLoader.CanonicalBytes(first.Policy));
        var northStar = canonical.RootElement.GetProperty("north_star");
        Assert.Equal("two hearts", northStar.GetProperty("target").GetString());
        Assert.Equal("aspirational-not-direct", northStar.GetProperty("policy").GetString());
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

    public static TheoryData<string> RepositoryMissionCases => new()
    {
        "canonical",
        "measured:novelty:D5-T0040",
        "measured:dependency_readiness:D5-T0041",
        "measured:structural_realization:D5-T0042",
        "measured:receipt_potential:D5-T0043",
        "measured:all",
        "north_star:target",
        "north_star:policy",
        "value_order:unknown",
        "value_order:missing",
        "value_order:duplicate",
        "value_order:reordered",
        "prohibitions:unknown",
        "prohibitions:missing",
        "prohibitions:duplicate",
        "prohibitions:reordered",
        "format:bom",
        "format:crlf",
        "format:missing-final-lf",
        "format:invalid-utf8",
        "schema:root:unknown",
        "schema:root:duplicate",
        "schema:root:missing",
        "schema:north_star:unknown",
        "schema:north_star:duplicate",
        "schema:north_star:missing",
        "schema:selection:unknown",
        "schema:selection:duplicate",
        "schema:selection:missing",
        "tie_break",
        "ticket:missing-task-block",
    };

    [Theory]
    [MemberData(nameof(RepositoryMissionCases))]
    public void RepositoryMissionContractIsTypedAndFailClosed(string scenario)
    {
        if (scenario != "canonical")
        {
            var fixture = RepositoryScenario(scenario);
            var invalid = Assert.IsType<MissionLoadOutcome.Invalid>(
                LoadRepository(fixture.Mission, fixture.Target));

            Assert.Equal(fixture.ErrorCode, invalid.Error.Code);
            if (fixture.MessageFragment is not null)
            {
                Assert.Contains(fixture.MessageFragment, invalid.Error.Message, StringComparison.Ordinal);
            }

            return;
        }

        var root = TestRepositoryLayout.FindRoot();
        var loaded = Assert.IsType<MissionLoadOutcome.Loaded>(
            MissionFileLoader.LoadRepository(root));

        Assert.Equal(4, loaded.Policy.WorthVector.Factors.Length);
        Assert.All(
            loaded.Policy.WorthVector.Factors,
            factor => Assert.IsType<WorthFactorState.Open>(factor.State));
        Assert.Equal("MissionNorthStarTarget", loaded.Policy.NorthStarTarget.GetType().Name);
        Assert.Equal("TwoHearts", loaded.Policy.NorthStarTarget.ToString());
        Assert.Equal("MissionNorthStarPolicy", loaded.Policy.NorthStarPolicy.GetType().Name);
        Assert.Equal("AspirationalNotDirect", loaded.Policy.NorthStarPolicy.ToString());
        Assert.Equal(
            ["UnderstandingOverQuantity", "HonestyOverSpeed", "NegativeKnowledgeEqualsPositiveResults"],
            loaded.Policy.ValueOrder.Select(static value => value.ToString()));
        Assert.All(loaded.Policy.ValueOrder, static value => Assert.IsNotType<string>((object)value));
        Assert.Equal(
            ["SorryCountOptimization", "TrivialLemmaAccumulation", "CitationChasing"],
            loaded.Policy.Prohibitions.Select(static value => value.ToString()));
        Assert.All(loaded.Policy.Prohibitions, static value => Assert.IsNotType<string>((object)value));
    }

    private static RepositoryCase RepositoryScenario(string scenario)
    {
        if (scenario.StartsWith("measured:", StringComparison.Ordinal)
            && scenario is not "measured:all")
        {
            var parts = scenario.Split(':');
            return Case(
                WithMeasuredFactor(ValidMission, parts[1], parts[2]),
                MissionLoadErrorCode.InvalidWorthState,
                parts[2]);
        }

        if (scenario.StartsWith("value_order:", StringComparison.Ordinal))
        {
            return ChangedCase(
                MutateValueOrder(scenario["value_order:".Length..]),
                MissionLoadErrorCode.InvalidSchema);
        }

        if (scenario.StartsWith("prohibitions:", StringComparison.Ordinal))
        {
            return ChangedCase(
                MutateProhibitions(scenario["prohibitions:".Length..]),
                MissionLoadErrorCode.InvalidSchema);
        }

        if (scenario.StartsWith("schema:", StringComparison.Ordinal))
        {
            var parts = scenario.Split(':');
            return ChangedCase(
                MutateObjectLayer(parts[1], parts[2]),
                parts[1] == "selection"
                    ? MissionLoadErrorCode.InvalidSelection
                    : MissionLoadErrorCode.InvalidSchema);
        }

        return scenario switch
        {
            "measured:all" => Case(
                AllMeasuredMission(),
                MissionLoadErrorCode.InvalidWorthState,
                "D5-T0040"),
            "north_star:target" => ChangedCase(
                ValidMission.Replace("\"two hearts\"", "\"three hearts\"", StringComparison.Ordinal),
                MissionLoadErrorCode.InvalidSchema),
            "north_star:policy" => ChangedCase(
                ValidMission.Replace(
                    "\"aspirational-not-direct\"",
                    "\"direct\"",
                    StringComparison.Ordinal),
                MissionLoadErrorCode.InvalidSchema),
            "format:bom" => BytesCase(
                Encoding.UTF8.GetPreamble().Concat(Encoding.UTF8.GetBytes(ValidMission)).ToArray(),
                MissionLoadErrorCode.InvalidFormat),
            "format:crlf" => BytesCase(
                Encoding.UTF8.GetBytes(ValidMission.Replace("\n", "\r\n", StringComparison.Ordinal)),
                MissionLoadErrorCode.InvalidFormat),
            "format:missing-final-lf" => BytesCase(
                Encoding.UTF8.GetBytes(ValidMission.TrimEnd('\n')),
                MissionLoadErrorCode.InvalidFormat),
            "format:invalid-utf8" => BytesCase(
                Encoding.UTF8.GetBytes(ValidMission)[..^1].Append((byte)0xff).ToArray(),
                MissionLoadErrorCode.InvalidFormat),
            "tie_break" => ChangedCase(
                ValidMission.Replace(
                    "canonical candidate id",
                    "display order",
                    StringComparison.Ordinal),
                MissionLoadErrorCode.InvalidSelection),
            "ticket:missing-task-block" => Case(
                ValidMission,
                MissionLoadErrorCode.DanglingCaseReference,
                "D5-T0040",
                ReplaceNoveltyTaskBlock(
                    "/-- receipt contract is not a TASK block -/\n"
                    + "def missionNoveltyMeasurementTicket : Unit := ()")),
            _ => throw new ArgumentOutOfRangeException(nameof(scenario), scenario, null),
        };
    }

    private static RepositoryCase ChangedCase(string mission, MissionLoadErrorCode errorCode)
    {
        Assert.NotEqual(ValidMission, mission);
        return Case(mission, errorCode);
    }

    private static RepositoryCase Case(
        string mission,
        MissionLoadErrorCode errorCode,
        string? messageFragment = null,
        string? target = null) =>
        BytesCase(Encoding.UTF8.GetBytes(mission), errorCode, messageFragment, target);

    private static RepositoryCase BytesCase(
        byte[] mission,
        MissionLoadErrorCode errorCode,
        string? messageFragment = null,
        string? target = null) =>
        new(mission, target, errorCode, messageFragment);

    private sealed record RepositoryCase(
        byte[] Mission,
        string? Target,
        MissionLoadErrorCode ErrorCode,
        string? MessageFragment);

    private static string WithMeasuredFactor(string mission, string factor, string caseId) =>
        mission.Replace(
            $"\"{factor}\": {{ \"state\": \"open\", \"case_id\": \"{caseId}\" }}",
            $"\"{factor}\": {{ \"state\": \"measured\", \"value\": 1.25, \"receipt_ref\": \"receipt:invented:{factor}\" }}",
            StringComparison.Ordinal);

    private static string AllMeasuredMission()
    {
        var mission = ValidMission;
        foreach (var (factor, caseId) in new[]
                 {
                     ("novelty", "D5-T0040"),
                     ("dependency_readiness", "D5-T0041"),
                     ("structural_realization", "D5-T0042"),
                     ("receipt_potential", "D5-T0043"),
                 })
        {
            mission = WithMeasuredFactor(mission, factor, caseId);
        }

        return mission.Replace(
            "bootstrap eligibility order",
            "complete worth argmax",
            StringComparison.Ordinal);
    }

    private static string MutateValueOrder(string mutation) => mutation switch
    {
        "unknown" => ValidMission.Replace(
            "understanding-over-quantity",
            "quantity-over-understanding",
            StringComparison.Ordinal),
        "missing" => ValidMission.Replace(
            "\"honesty-over-speed\",",
            string.Empty,
            StringComparison.Ordinal),
        "duplicate" => ValidMission.Replace(
            "negative-knowledge-equals-positive-results",
            "honesty-over-speed",
            StringComparison.Ordinal),
        "reordered" => ValidMission
            .Replace("understanding-over-quantity", "value-order-placeholder", StringComparison.Ordinal)
            .Replace("honesty-over-speed", "understanding-over-quantity", StringComparison.Ordinal)
            .Replace("value-order-placeholder", "honesty-over-speed", StringComparison.Ordinal),
        _ => throw new ArgumentOutOfRangeException(nameof(mutation), mutation, null),
    };

    private static string MutateProhibitions(string mutation) => mutation switch
    {
        "unknown" => ValidMission.Replace(
            "sorry-count optimization",
            "proof-count optimization",
            StringComparison.Ordinal),
        "missing" => ValidMission.Replace(
            "\"trivial-lemma accumulation\",",
            string.Empty,
            StringComparison.Ordinal),
        "duplicate" => ValidMission.Replace(
            "citation chasing",
            "trivial-lemma accumulation",
            StringComparison.Ordinal),
        "reordered" => ValidMission
            .Replace("sorry-count optimization", "prohibition-placeholder", StringComparison.Ordinal)
            .Replace("trivial-lemma accumulation", "sorry-count optimization", StringComparison.Ordinal)
            .Replace("prohibition-placeholder", "trivial-lemma accumulation", StringComparison.Ordinal),
        _ => throw new ArgumentOutOfRangeException(nameof(mutation), mutation, null),
    };

    private static string MutateObjectLayer(string layer, string mutation) => (layer, mutation) switch
    {
        ("root", "unknown") => ValidMission.Replace(
            "  \"schema\": \"trureturing-mission-v1\",",
            "  \"schema\": \"trureturing-mission-v1\",\n  \"unknown\": true,",
            StringComparison.Ordinal),
        ("root", "duplicate") => ValidMission.Replace(
            "  \"schema\": \"trureturing-mission-v1\",",
            "  \"schema\": \"trureturing-mission-v1\",\n  \"schema\": \"trureturing-mission-v1\",",
            StringComparison.Ordinal),
        ("root", "missing") => ValidMission.Replace(
            "  \"schema\": \"trureturing-mission-v1\",\n",
            string.Empty,
            StringComparison.Ordinal),
        ("north_star", "unknown") => ValidMission.Replace(
            "    \"policy\": \"aspirational-not-direct\"",
            "    \"policy\": \"aspirational-not-direct\",\n    \"unknown\": true",
            StringComparison.Ordinal),
        ("north_star", "duplicate") => ValidMission.Replace(
            "    \"target\": \"two hearts\",",
            "    \"target\": \"two hearts\",\n    \"target\": \"two hearts\",",
            StringComparison.Ordinal),
        ("north_star", "missing") => ValidMission.Replace(
            "    \"target\": \"two hearts\",\n    \"policy\": \"aspirational-not-direct\"",
            "    \"target\": \"two hearts\"",
            StringComparison.Ordinal),
        ("selection", "unknown") => ValidMission.Replace(
            "    \"tie_break\": \"canonical candidate id\"",
            "    \"tie_break\": \"canonical candidate id\",\n    \"unknown\": true",
            StringComparison.Ordinal),
        ("selection", "duplicate") => ValidMission.Replace(
            "    \"tie_break\": \"canonical candidate id\"",
            "    \"tie_break\": \"canonical candidate id\",\n    \"tie_break\": \"canonical candidate id\"",
            StringComparison.Ordinal),
        ("selection", "missing") => ValidMission.Replace(
            "    \"order_kind\": \"bootstrap eligibility order\",\n    \"tie_break\": \"canonical candidate id\"",
            "    \"tie_break\": \"canonical candidate id\"",
            StringComparison.Ordinal),
        _ => throw new ArgumentOutOfRangeException(nameof(mutation), $"{layer}/{mutation}", null),
    };

    private static MissionLoadOutcome LoadRepository(byte[] mission, string? target = null)
    {
        using var repository = new TemporaryDirectory();
        ReviewRegressionTests.RunGit(repository.Path, "init", "--quiet");
        WriteFile(repository.Path, BackfillInventoryLoader.TicketIndexPath, Encoding.UTF8.GetBytes(TicketIndex));
        WriteFile(
            repository.Path,
            "D5/X_Frontier/GovernanceDeferrals.lean",
            Encoding.UTF8.GetBytes(target ?? GovernanceDeferrals));
        WriteFile(repository.Path, MissionFileLoader.RelativePath, mission);
        ReviewRegressionTests.RunGit(repository.Path, "add", ".");
        return MissionFileLoader.LoadRepository(repository.Path);
    }

    private static string ReplaceNoveltyTaskBlock(string replacement)
    {
        var result = GovernanceDeferrals.Replace(
            NoveltyTaskBlock,
            replacement,
            StringComparison.Ordinal);
        Assert.NotEqual(GovernanceDeferrals, result);
        return result;
    }

    private static void WriteFile(string root, string relativePath, byte[] contents)
    {
        var path = Path.Combine(root, relativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllBytes(path, contents);
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
