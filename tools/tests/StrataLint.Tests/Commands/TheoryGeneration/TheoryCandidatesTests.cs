using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TheoryCandidatesTests
{
    private const string MathematicalFrontierPath = "D5/X_Frontier/MathematicalProblem.lean";
    private const string GovernanceFrontierPath = "D5/X_Frontier/GovernanceTicket.lean";
    private const string NonFrontierOpenPath = "D5/S0/Carrier/UnfinishedFact.lean";
    private const string ResidualAtomPath =
        "Meta/Digestion/backfill/fixture-source/residual-open/fixture-atom.yaml";
    private const string PartialAtomPath =
        "Meta/Digestion/backfill/fixture-source/partial-open/partial-atom.yaml";
    private static readonly string FixtureMission = """
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
    public void EnumeratesOnlyMathematicalOpenFrontierAndDerivedResidualOpenAtoms()
    {
        var fixture = CandidateFixture();

        var result = Run(fixture);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        var candidates = json.RootElement.GetProperty("candidates").EnumerateArray().ToArray();
        Assert.Equal(
            ["atom/fixture-atom", "frontier/D5/X_Frontier/MathematicalProblem"],
            candidates.Select(static candidate => candidate.GetProperty("candidate_id").GetString()));
        Assert.DoesNotContain(candidates, candidate =>
            candidate.GetProperty("source_ref").GetString() is
                "D5/X_Frontier/GovernanceTicket" or "D5/S0/Carrier/UnfinishedFact" or "partial-atom");
        Assert.Equal(
            ["codex-formalize", "prover"],
            candidates.Select(static candidate => candidate.GetProperty("downstream_lane").GetString()));
        Assert.All(candidates, static candidate =>
            Assert.Equal(1, candidate.EnumerateObject().Count(static property =>
                property.NameEquals("downstream_lane"))));
    }

    [Fact]
    public void FrontierClassifierKeepsEveryFailureDirectionDistinct()
    {
        var fixture = CandidateFixture();
        var (snapshot, dag) = Truth(fixture);
        var ticketModules = BackfillInventoryLoader.DeriveTickets(snapshot)
            .Select(static ticket => ticket.Gid)
            .ToHashSet(StringComparer.Ordinal);

        Assert.Equal(
            FrontierCandidateClassification.MathematicalOpen,
            Classify(MathematicalFrontierPath));
        Assert.Equal(
            FrontierCandidateClassification.GovernanceTicket,
            Classify(GovernanceFrontierPath));
        Assert.Equal(
            FrontierCandidateClassification.OutsideFrontier,
            Classify(NonFrontierOpenPath));
        Assert.Equal(
            FrontierCandidateClassification.NotOpen,
            Classify(RuleFixture.RingPath));

        FrontierCandidateClassification Classify(string path) =>
            TheoryCandidatesCommand.ClassifyFrontier(
                dag.Nodes.Single(node => node.RepoPath.Value == path),
                ticketModules);
    }

    [Fact]
    public void OwnerOverrideIsContentAddressedAndCannotMasqueradeAsRepositoryOrdering()
    {
        var fixture = CandidateFixture();
        const string problem = "Classify the fixed points of the observer quotient.";

        var first = Run(fixture, "--owner-override", problem);
        var replay = Run(fixture, "--owner-override", problem);

        Assert.True(first.Success, first.Error);
        Assert.Equal(Encoding.UTF8.GetBytes(first.Output), Encoding.UTF8.GetBytes(replay.Output));
        using var json = JsonDocument.Parse(first.Output);
        var root = json.RootElement;
        var receipt = root.GetProperty("selection_receipt");
        var owner = Assert.Single(root.GetProperty("candidates").EnumerateArray(), static candidate =>
            candidate.GetProperty("source_kind").GetString() == "owner_override");
        var problemSha256 = "sha256:" + Convert.ToHexStringLower(
            SHA256.HashData(Encoding.UTF8.GetBytes(problem)));
        Assert.Equal(problemSha256, owner.GetProperty("content_sha256").GetString());
        Assert.Equal(problem, owner.GetProperty("problem_text").GetString());
        Assert.Equal("owner_override", receipt.GetProperty("selection_mode").GetString());
        Assert.Equal(owner.GetProperty("candidate_id").GetString(),
            receipt.GetProperty("selected_candidate_id").GetString());
        Assert.DoesNotContain("worth", first.Output, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("argmax", first.Output, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void CanonicalOrderingAndReceiptHashesAreReplayStable()
    {
        var fixture = CandidateFixture();

        var first = Run(fixture);
        var replay = RunCore(fixture, reverseSnapshotEntries: true);

        Assert.True(first.Success, first.Error);
        Assert.Equal(Encoding.UTF8.GetBytes(first.Output), Encoding.UTF8.GetBytes(replay.Output));
        using var json = JsonDocument.Parse(first.Output);
        var root = json.RootElement;
        var candidates = root.GetProperty("candidates");
        var ids = candidates.EnumerateArray()
            .Select(static candidate => candidate.GetProperty("candidate_id").GetString())
            .ToArray();
        Assert.Equal(ids.Order(StringComparer.Ordinal), ids);
        var expectedCandidateSetSha256 = CandidateSetSha256(candidates);
        var receipt = root.GetProperty("selection_receipt");
        Assert.Equal(expectedCandidateSetSha256,
            receipt.GetProperty("candidate_set_sha256").GetString());
        Assert.Matches("^sha256:[0-9a-f]{64}$",
            receipt.GetProperty("input_snapshot_sha256").GetString());
        Assert.Equal("theory-candidates-bootstrap-v1",
            receipt.GetProperty("ordering_version").GetString());
        Assert.Equal("bootstrap eligibility order",
            receipt.GetProperty("order_kind").GetString());
        Assert.Equal("canonical candidate id", receipt.GetProperty("tie_break").GetString());
        Assert.Equal(ids[0], receipt.GetProperty("selected_candidate_id").GetString());
        Assert.DoesNotContain("worth", first.Output, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("argmax", first.Output, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void NonBootstrapMissionSelectionFailsClosedBeforeProjection()
    {
        var fixture = CandidateFixture();
        var (snapshot, _) = Truth(fixture);
        var loaded = Assert.IsType<MissionLoadOutcome.Loaded>(MissionFileLoader.Load(snapshot));
        var unsupported = loaded.Policy with
        {
            Selection = new MissionSelectionPolicy(
                WorthSelectionOrder.CompleteWorthArgmax,
                loaded.Policy.Selection.TieBreak),
        };

        var exception = Assert.Throws<InvalidOperationException>(() =>
            TheoryCandidateProjection.Render(
                "sha256:" + new string('0', 64),
                unsupported,
                [],
                ownerOverride: null));

        Assert.Contains("bootstrap selection is unavailable", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CommandRejectsMissingMissionAndMalformedArguments()
    {
        var fixture = CandidateFixture();
        fixture.Files.Remove(MissionFileLoader.RelativePath);

        var missing = Run(fixture);
        var duplicate = Run(CandidateFixture(), "--owner-override", "first", "--owner-override", "second");

        Assert.False(missing.Success);
        Assert.Empty(missing.Output);
        Assert.Contains("MISSION file is missing", missing.Error, StringComparison.Ordinal);
        Assert.False(duplicate.Success);
        Assert.Empty(duplicate.Output);
        Assert.Contains("USAGE: StrataLint theory-candidates", duplicate.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionQueryLeavesItsRepositoryRootByteIdentical()
    {
        using var directory = new TemporaryDirectory();
        Assert.Empty(Directory.GetFileSystemEntries(directory.Path));

        var result = RunCore(CandidateFixture(), repositoryRoot: directory.Path);

        Assert.True(result.Success, result.Error);
        Assert.Empty(Directory.GetFileSystemEntries(directory.Path));
    }

    private static CommandResult Run(
        RuleFixture fixture,
        params string[] arguments) =>
        RunCore(fixture, arguments, reverseSnapshotEntries: false, repositoryRoot: "/repo");

    private static CommandResult RunCore(
        RuleFixture fixture,
        IReadOnlyList<string>? arguments = null,
        bool reverseSnapshotEntries = false,
        string repositoryRoot = "/repo")
    {
        var entries = reverseSnapshotEntries
            ? fixture.Files.Reverse().Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value))
            : fixture.Files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value));
        var environment = new ProductionCliEnvironment(
            repositoryRoot,
            new FakeRepositoryGateway(
                RawChangeSet.Create([]),
                RawRepositorySnapshot.Create(entries),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));
        return environment.TheoryCandidates(arguments ?? []);
    }

    private static (RepositorySnapshot Snapshot, AcyclicTruthDag Dag) Truth(RuleFixture fixture)
    {
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(fixture.Files.Select(static pair =>
                RawRepositoryEntry.FromText(pair.Key, pair.Value))))).Snapshot;
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(LeanClosureValidator.Validate(
            snapshot,
            LeanAxiomReport.Create(fixture.Reports))).Capability;
        var dag = Assert.IsType<DagBuildOutcome.Accepted>(AcyclicTruthDag.Build(snapshot, lean)).Capability;
        return (snapshot, dag);
    }

    private static RuleFixture CandidateFixture()
    {
        var fixture = new RuleFixture();
        fixture.Files.Remove(RuleFixture.FixtureBackfillAtomPath);
        fixture.Files[ResidualAtomPath] = RuleFixture.FixtureBackfillAtom.Replace(
            "coverage_gids:\n  - D5/S0/Carrier/BackfillTarget",
            "coverage_gids: []",
            StringComparison.Ordinal);
        fixture.Files[PartialAtomPath] = RuleFixture.FixtureBackfillAtom
            .Replace("manual/fixture", "manual/partial", StringComparison.Ordinal)
            .Replace(
                "D5/S0/Carrier/BackfillTarget",
                "D5/X_Frontier/MathematicalProblem",
                StringComparison.Ordinal);
        fixture.Files[MissionFileLoader.RelativePath] = FixtureMission;
        fixture.Files["D5/X_Frontier/MissionTickets.lean"] = string.Concat(
            Enumerable.Range(40, 4).Select(static number =>
                $"/-- TASK D5-T{number:0000}\n    Measurement contract remains open. -/\n"
                + $"def missionTicket{number:0000} : Unit := ()\n"));
        fixture.Files[MathematicalFrontierPath] = "def mathematicalProblem : Prop := True\n";
        fixture.Files[GovernanceFrontierPath] =
            "/- TASK D5-T0100\n    Harness work item. -/\ndef governanceTicket : Unit := ()\n";
        fixture.Files[NonFrontierOpenPath] = "theorem unfinishedFact : True := by sorry\n";
        fixture.Reports["D5/X_Frontier/MissionTickets.lean"] = EmptyReport();
        fixture.Reports[MathematicalFrontierPath] = EmptyReport();
        fixture.Reports[GovernanceFrontierPath] = EmptyReport();
        fixture.Reports[NonFrontierOpenPath] = new LeanFileReport(
            [],
            [new LeanDeclaration("unfinishedFact", "theorem", "True", ["sorryAx"])]);
        return fixture;
    }

    private static LeanFileReport EmptyReport() => new([], []);

    private static string CandidateSetSha256(JsonElement candidates)
    {
        var canonical = StructuredCanonicalWriter.WriteJson(candidates);
        var prefix = Encoding.UTF8.GetBytes("theory-candidate-set-v1\0");
        return "sha256:" + Convert.ToHexStringLower(SHA256.HashData(
            prefix.Concat(canonical).ToArray()));
    }
}
