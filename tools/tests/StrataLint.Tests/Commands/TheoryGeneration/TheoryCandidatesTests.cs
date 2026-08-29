using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Tests;

public sealed partial class TheoryCandidatesTests
{
    private const string MathematicalFrontierPath = "D5/X_Frontier/FrontierMathematicalOpen.lean";
    private const string DeclarationReadyFrontierPath = "D5/X_Frontier/Hearts.lean";
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
            "novelty": { "state": "open" },
            "dependency_readiness": { "state": "open" },
            "structural_realization": { "state": "open" },
            "receipt_potential": { "state": "open" }
          },
          "frontier_eligibility": [
            {
              "source_ref": "D5/X_Frontier/FrontierMathematicalOpen",
              "kind": "mathematical-not-yet-stated"
            },
            {
              "source_ref": "D5/X_Frontier/GovernanceTicket",
              "kind": "governance"
            },
            {
              "source_ref": "D5/X_Frontier/Hearts",
              "kind": "declaration-ready-mathematical-open"
            }
          ],
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
    public void UnrelatedChangeDoesNotReplayCommittedProjectedStatus()
    {
        var result = RunCore(
            CandidateFixtureWithMismatchedProjectedStatus(),
            changes: RawChangeSet.Create(["notes/r16-unrelated.txt"]));

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Contains(
            json.RootElement.GetProperty("candidates").EnumerateArray(),
            static candidate => candidate.GetProperty("candidate_id").GetString() == "atom/fixture-atom");
    }

    [Fact]
    public void ChangedDigestionEntryStillValidatesProjectedStatus()
    {
        var fixture = CandidateFixtureWithMismatchedProjectedStatus();
        const string changedPath =
            "Meta/Digestion/backfill/fixture-source/absorbed-closed/fixture-atom.yaml";

        var result = RunCore(fixture, changes: RawChangeSet.Create([changedPath]));

        Assert.False(result.Success);
        Assert.Contains("handwritten status", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestionImplementationChangeStillReplaysCommittedProjectedStatus()
    {
        var result = RunCore(
            CandidateFixtureWithMismatchedProjectedStatus(),
            changes: RawChangeSet.Create(
            ["tools/StrataLint.Engine/Digestion/Evaluation/DigestionStatusEvaluator.cs"]));

        Assert.False(result.Success);
        Assert.Contains("handwritten status", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void UnrelatedChangeDoesNotReplayCommittedCasIntegrity()
    {
        var fixture = CandidateFixture();
        fixture.Files[RuleFixture.FixtureCasPath] = "tampered committed CAS bytes";

        var result = RunCore(
            fixture,
            changes: RawChangeSet.Create(["notes/r17-unrelated-cas.txt"]));

        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain("CAS blob hash mismatch", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ChangedCasStillValidatesCommittedCasIntegrity()
    {
        var fixture = CandidateFixture();
        fixture.Files[RuleFixture.FixtureCasPath] = "tampered changed CAS bytes";

        var result = RunCore(
            fixture,
            changes: RawChangeSet.Create([RuleFixture.FixtureCasPath]));

        Assert.False(result.Success);
        Assert.Contains("CAS blob hash mismatch", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestionImplementationChangeStillReplaysCommittedCasIntegrity()
    {
        var fixture = CandidateFixture();
        fixture.Files[RuleFixture.FixtureCasPath] = "tampered committed CAS bytes";

        var result = RunCore(
            fixture,
            changes: RawChangeSet.Create(
            ["tools/StrataLint.Engine/Digestion/Evaluation/DigestionStatusEvaluator.cs"]));

        Assert.False(result.Success);
        Assert.Contains("CAS blob hash mismatch", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void UnrelatedChangeDoesNotReplayCommittedSourceMetadataCanonicalEncoding()
    {
        var fixture = CandidateFixtureWithNoncanonicalSourceMetadata();

        var result = RunCore(
            fixture,
            changes: RawChangeSet.Create(["notes/r17-unrelated-source-metadata.txt"]));

        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain("source metadata is not canonically encoded", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ChangedSourceMetadataStillValidatesCanonicalEncoding()
    {
        var fixture = CandidateFixtureWithNoncanonicalSourceMetadata();

        var result = RunCore(
            fixture,
            changes: RawChangeSet.Create([RuleFixture.FixtureBackfillSourcePath]));

        Assert.False(result.Success);
        Assert.Contains("source metadata is not canonically encoded", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ChangedSourceMetadataWriterInputStillValidatesCanonicalEncoding()
    {
        var fixture = CandidateFixtureWithNoncanonicalSourceMetadata();

        var result = RunCore(
            fixture,
            changes: RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath]));

        Assert.False(result.Success);
        Assert.Contains("source metadata is not canonically encoded", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestionImplementationChangeStillReplaysSourceMetadataCanonicalEncoding()
    {
        var fixture = CandidateFixtureWithNoncanonicalSourceMetadata();

        var result = RunCore(
            fixture,
            changes: RawChangeSet.Create(
            ["tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryWriter.cs"]));

        Assert.False(result.Success);
        Assert.Contains("source metadata is not canonically encoded", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void EnumeratesOnlyMathematicalOpenFrontierAndDerivedResidualOpenAtoms()
    {
        var fixture = CandidateFixture();

        var result = Run(fixture);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        var candidates = json.RootElement.GetProperty("candidates").EnumerateArray().ToArray();
        Assert.Equal(
            [
                "atom/fixture-atom",
                "frontier/D5/X_Frontier/FrontierMathematicalOpen",
                "frontier/D5/X_Frontier/Hearts.o5_independence",
                "frontier/D5/X_Frontier/Hearts.o6WeilPositivityStatement",
            ],
            candidates.Select(static candidate => candidate.GetProperty("candidate_id").GetString()));
        Assert.True(
            candidates.Count(candidate => candidate.GetProperty("source_ref").GetString() is
                "D5/X_Frontier/GovernanceTicket" or "D5/S0/Carrier/UnfinishedFact" or "partial-atom") == 0,
            "Expected no candidate with source_ref in "
                + "{D5/X_Frontier/GovernanceTicket, D5/S0/Carrier/UnfinishedFact, partial-atom}; "
                + "matched forbidden source_ref(s): "
                + string.Join(
                    ", ",
                    candidates
                        .Where(candidate => candidate.GetProperty("source_ref").GetString() is
                            "D5/X_Frontier/GovernanceTicket"
                            or "D5/S0/Carrier/UnfinishedFact"
                            or "partial-atom")
                        .Select(static candidate => candidate.GetProperty("source_ref").GetString())
                        .Order(StringComparer.Ordinal))
                + "; actual candidates: "
                + CandidateInventory(candidates));
        Assert.DoesNotContain(candidates, candidate =>
            candidate.GetProperty("source_ref").GetString() is
                "D5/X_Frontier/GovernanceTicket" or "D5/S0/Carrier/UnfinishedFact" or "partial-atom");
        Assert.Equal(
            ["codex-formalize", "theorist", "prover", "prover"],
            candidates.Select(static candidate => candidate.GetProperty("downstream_lane").GetString()));
        Assert.All(candidates, static candidate =>
        {
            var downstreamLaneCount = candidate.EnumerateObject().Count(static property =>
                property.NameEquals("downstream_lane"));
            Assert.True(
                downstreamLaneCount == 1,
                $"Expected exactly one downstream_lane field for candidate "
                + $"source_ref={candidate.GetProperty("source_ref").GetString()}|"
                + $"source_kind={candidate.GetProperty("source_kind").GetString()}; "
                + $"actual downstream_lane field count={downstreamLaneCount}");
            Assert.Equal(1, downstreamLaneCount);
        });
    }

    [Fact]
    public void DeclarationReadyFrontierEmitsOneAddressedCandidatePerOpenProposition()
    {
        var fixture = CandidateFixture();
        var report = fixture.Reports[DeclarationReadyFrontierPath];
        var path = RepoPath.CreateKnown(DeclarationReadyFrontierPath);
        var statements = CanonicalStatementWriter.DeclarationStatementIds(path, report)
            .ToDictionary(static statement => statement.DeclarationNameKey, StringComparer.Ordinal);
        var lazyFixture = CandidateFixture();
        var loaded = 0;
        lazyFixture.Reports[DeclarationReadyFrontierPath] = new LeanFileReport(
            report.Imports,
            report.Declarations.Select(declaration =>
            {
                var material = declaration.TypeRepresentation;
                return new LeanDeclaration(
                    declaration.Name,
                    declaration.Kind,
                    CanonicalStatementWriter.StatementTypeAddress(declaration),
                    CanonicalStatementWriter.DeclarationStatementId(path, declaration),
                    declaration.Axioms,
                    () =>
                    {
                        loaded++;
                        return material;
                    })
                {
                    IncludeInStatement = declaration.IncludeInStatement,
                    NameKey = declaration.NameKey,
                };
            }).ToImmutableArray());

        var result = Run(fixture);
        var lazyResult = Run(lazyFixture);

        Assert.True(result.Success, result.Error);
        Assert.True(lazyResult.Success, lazyResult.Error);
        Assert.Equal(result.Output, lazyResult.Output);
        Assert.Equal(2, loaded);
        using var json = JsonDocument.Parse(result.Output);
        var candidates = json.RootElement.GetProperty("candidates").EnumerateArray()
            .Where(static candidate => candidate.GetProperty("downstream_lane").GetString() == "prover")
            .ToDictionary(
                static candidate => candidate.GetProperty("source_ref").GetString()!,
                StringComparer.Ordinal);
        Assert.Equal(
            [
                "D5/X_Frontier/Hearts.o5_independence",
                "D5/X_Frontier/Hearts.o6WeilPositivityStatement",
            ],
            candidates.Keys.Order(StringComparer.Ordinal));
        Assert.Equal(
            "frontier/D5/X_Frontier/Hearts.o5_independence",
            candidates["D5/X_Frontier/Hearts.o5_independence"]
                .GetProperty("candidate_id").GetString());
        Assert.Equal(
            statements[report.Declarations.Single(static declaration =>
                    declaration.Name.EndsWith(".o5_independence", StringComparison.Ordinal)).NameKey]
                .StatementId.Value,
            candidates["D5/X_Frontier/Hearts.o5_independence"]
                .GetProperty("content_sha256").GetString());
        Assert.Equal(
            statements[report.Declarations.Single(static declaration =>
                    declaration.Name.EndsWith(".o6WeilPositivityStatement", StringComparison.Ordinal)).NameKey]
                .StatementId.Value,
            candidates["D5/X_Frontier/Hearts.o6WeilPositivityStatement"]
                .GetProperty("content_sha256").GetString());

        // The V2 contract's exact_statement.statement_sha256 is the type-only
        // address; the producer issues it so the theorize seat copies rather than
        // hand-hashes. Fixed literals derived independently with openssl over
        // "trureturing:statement:v1" NUL + the fixture's .type bytes.
        Assert.Equal(
            "sha256:23d46af0b4d3e7843f042c1fd5dedc8b9fa6f670ad588c2218152d135e08ef75",
            candidates["D5/X_Frontier/Hearts.o5_independence"]
                .GetProperty("statement_type_sha256").GetString());
        Assert.Equal(
            "sha256:33bff61cf92a4581cc99dbc5e78e3032b32dbff52827d906a5bb629f511efd63",
            candidates["D5/X_Frontier/Hearts.o6WeilPositivityStatement"]
                .GetProperty("statement_type_sha256").GetString());
    }

    [Fact]
    public void FrontierClassifierKeepsEveryFailureDirectionDistinct()
    {
        var fixture = CandidateFixture();
        var (snapshot, dag) = Truth(fixture);
        var mission = Assert.IsType<MissionLoadOutcome.Loaded>(MissionFileLoader.Load(snapshot)).Policy;
        var eligibility = mission.FrontierEligibility.ToDictionary(
            static entry => entry.SourceRef,
            static entry => entry.Kind,
            StringComparer.Ordinal);

        Assert.Equal(
            FrontierCandidateClassification.MathematicalNotYetStated,
            Classify(MathematicalFrontierPath));
        Assert.Equal(
            FrontierCandidateClassification.Governance,
            Classify(GovernanceFrontierPath));
        Assert.Equal(
            FrontierCandidateClassification.OutsideFrontier,
            Classify(NonFrontierOpenPath));
        Assert.Equal(
            FrontierCandidateClassification.NotOpen,
            Classify(RuleFixture.RingPath));

        FrontierCandidateClassification Classify(string path) =>
            TheoryCandidatesCommand.ClassifyFrontier(
                ToFrontierNode(dag.Nodes.Single(node => node.RepoPath.Value == path)),
                eligibility);

        static FrontierStateNode ToFrontierNode(TruthProjectionNode node) =>
            new(node.RepoPath, node.Gid, node.State);
    }

    [Fact]
    public void GoldenUnitsUfdTaskAddressDoesNotChangeItsMathematicalEligibility()
    {
        var fixture = CandidateFixture();
        var (snapshot, dag) = Truth(fixture);
        var mission = Assert.IsType<MissionLoadOutcome.Loaded>(MissionFileLoader.Load(snapshot)).Policy;
        var eligibility = mission.FrontierEligibility.ToDictionary(
            static entry => entry.SourceRef,
            static entry => entry.Kind,
            StringComparer.Ordinal);

        var classification = TheoryCandidatesCommand.ClassifyFrontier(
            new FrontierStateNode(
                dag.Nodes.Single(node => node.RepoPath.Value == MathematicalFrontierPath).RepoPath,
                dag.Nodes.Single(node => node.RepoPath.Value == MathematicalFrontierPath).Gid,
                dag.Nodes.Single(node => node.RepoPath.Value == MathematicalFrontierPath).State),
            eligibility);

        Assert.Equal(FrontierCandidateClassification.MathematicalNotYetStated, classification);
    }

    [Fact]
    public void TheoristOnlySourceChangeCannotIssueDeclarationReadyOwnership()
    {
        var fixture = CandidateFixture();
        fixture.Files[MathematicalFrontierPath] =
            "theorem generated_open : True := by sorry\n";
        fixture.Reports[MathematicalFrontierPath] = new LeanFileReport(
            [],
            [
                new LeanDeclaration(
                    "D5.X_Frontier.FrontierMathematicalOpen.generated_open",
                    "theorem",
                    "statement-v1(uparams=[],type=ec(ns(n0,4:True),[]))",
                    ["sorryAx"]),
            ]);

        var result = Run(fixture);

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.True(
            json.RootElement.GetProperty("candidates").EnumerateArray().Count(static item =>
                item.GetProperty("source_ref").GetString()
                    == "D5/X_Frontier/FrontierMathematicalOpen") == 1,
            "Expected exactly one candidate with source_ref="
                + "D5/X_Frontier/FrontierMathematicalOpen; actual candidates "
                + "(source_ref|source_kind|downstream_lane): "
                + CandidateInventory(json.RootElement.GetProperty("candidates").EnumerateArray()));
        var candidate = Assert.Single(
            json.RootElement.GetProperty("candidates").EnumerateArray(),
            static item => item.GetProperty("source_ref").GetString()
                == "D5/X_Frontier/FrontierMathematicalOpen");
        Assert.Equal("frontier_problem", candidate.GetProperty("source_kind").GetString());
        Assert.Equal("theorist", candidate.GetProperty("downstream_lane").GetString());
        Assert.True(
            json.RootElement.GetProperty("candidates").EnumerateArray().Count(static item =>
                item.GetProperty("source_ref").GetString()
                    == "D5/X_Frontier/FrontierMathematicalOpen.generated_open") == 0,
            "Expected no candidate with source_ref="
                + "D5/X_Frontier/FrontierMathematicalOpen.generated_open; actual candidates "
                + "(source_ref|source_kind|downstream_lane): "
                + CandidateInventory(json.RootElement.GetProperty("candidates").EnumerateArray()));
        Assert.DoesNotContain(
            json.RootElement.GetProperty("candidates").EnumerateArray(),
            static item => item.GetProperty("source_ref").GetString()
                == "D5/X_Frontier/FrontierMathematicalOpen.generated_open");
    }

    [Fact]
    public void RepositoryFrontierEligibilityCoversLiveCorpusAndKeepsTaskBearingKindsDistinct()
    {
        var root = TestRepositoryLayout.FindRoot();
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            GitRepositorySnapshotReader.ReadCurrent(root))).Snapshot;
        var mission = Assert.IsType<MissionLoadOutcome.Loaded>(MissionFileLoader.Load(snapshot)).Policy;
        var eligibility = mission.FrontierEligibility.ToDictionary(
            static entry => entry.SourceRef,
            static entry => entry.Kind,
            StringComparer.Ordinal);
        var frontierPaths = snapshot.Files.Keys
            .Select(static path => path.Value)
            .Where(static path => path.StartsWith("D5/X_Frontier/", StringComparison.Ordinal)
                && path.EndsWith(".lean", StringComparison.Ordinal))
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(
            frontierPaths,
            mission.FrontierEligibility
                .Where(entry => snapshot.TryGetFile(entry.SourceRef + ".lean", out _))
                .Select(static entry => entry.SourceRef + ".lean")
                .Order(StringComparer.Ordinal));
        Assert.Equal(
            FrontierCandidateClassification.MathematicalNotYetStated,
            Classify("D5/X_Frontier/ValuesProducer"));
        Assert.Equal(
            FrontierCandidateClassification.Governance,
            Classify("D5/X_Frontier/D5P001"));
        Assert.Equal(
            FrontierCandidateClassification.NotOpen,
            Classify("D5/X_Frontier/GoldenUnitsUFD"));
        FrontierCandidateClassification Classify(string sourceRef)
        {
            Assert.True(Gid.TryParse(sourceRef, out var gid));
            return TheoryCandidatesCommand.ClassifyFrontier(
                new FrontierStateNode(gid.Path, gid, TruthState.Open),
                eligibility);
        }
    }

    [Fact]
    public void OwnerOverrideIsContentAddressedAndCannotMasqueradeAsRepositoryOrdering()
    {
        var fixture = CandidateFixture();
        const string problem = "Does \"x\" imply $HOME and `id`?\nClassify ξ exactly.\n";
        using var directory = new TemporaryDirectory();
        var problemPath = Path.Combine(directory.Path, "owner-problem.txt");
        File.WriteAllBytes(problemPath, Encoding.UTF8.GetBytes(problem));

        var first = Run(fixture, "--owner-override-file", problemPath);
        var replay = Run(fixture, "--owner-override-file", problemPath);

        Assert.True(first.Success, first.Error);
        Assert.Equal(Encoding.UTF8.GetBytes(first.Output), Encoding.UTF8.GetBytes(replay.Output));
        using var json = JsonDocument.Parse(first.Output);
        var root = json.RootElement;
        var receipt = root.GetProperty("selection_receipt");
        Assert.True(
            root.GetProperty("candidates").EnumerateArray().Count(static candidate =>
                candidate.GetProperty("source_kind").GetString() == "owner_override") == 1,
            "Expected exactly one candidate with source_kind=owner_override; actual candidates "
                + "(source_ref|source_kind|downstream_lane): "
                + CandidateInventory(root.GetProperty("candidates").EnumerateArray()));
        var owner = Assert.Single(root.GetProperty("candidates").EnumerateArray(), static candidate =>
            candidate.GetProperty("source_kind").GetString() == "owner_override");
        var problemSha256 = "sha256:" + Convert.ToHexStringLower(
            SHA256.HashData(Encoding.UTF8.GetBytes(problem)));
        Assert.Equal(problemSha256, owner.GetProperty("content_sha256").GetString());
        Assert.Equal(problem, owner.GetProperty("problem_text").GetString());
        Assert.Equal("theorist", owner.GetProperty("downstream_lane").GetString());
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
        Assert.Matches("^sha256:[0-9a-f]{64}$",
            receipt.GetProperty("lean_report_sha256").GetString());
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
    public void OutputRootSchemaIsPinnedToTheoryCandidatesV1()
    {
        var result = Run(CandidateFixture());

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(
            "stratalint-theory-candidates-v1",
            json.RootElement.GetProperty("schema").GetString());
    }

    [Fact]
    public void LeanReportMaterialParticipatesInTheSelectionReceipt()
    {
        var baseline = CandidateFixture();
        var changedReport = CandidateFixture();
        changedReport.Reports[GovernanceFrontierPath] = new LeanFileReport(
            [],
            [new LeanDeclaration("governanceTicket", "def", "Unit", [])]);

        var first = Run(baseline);
        var changed = Run(changedReport);

        Assert.True(first.Success, first.Error);
        Assert.True(changed.Success, changed.Error);
        using var firstJson = JsonDocument.Parse(first.Output);
        using var changedJson = JsonDocument.Parse(changed.Output);
        var firstReceipt = firstJson.RootElement.GetProperty("selection_receipt");
        var changedReceipt = changedJson.RootElement.GetProperty("selection_receipt");
        Assert.Equal(
            firstReceipt.GetProperty("input_snapshot_sha256").GetString(),
            changedReceipt.GetProperty("input_snapshot_sha256").GetString());
        Assert.NotEqual(
            firstReceipt.GetProperty("lean_report_sha256").GetString(),
            changedReceipt.GetProperty("lean_report_sha256").GetString());
        Assert.Equal(
            firstReceipt.GetProperty("candidate_set_sha256").GetString(),
            changedReceipt.GetProperty("candidate_set_sha256").GetString());
    }

    [Fact]
    public void UnclassifiedFrontierFailsClosedInsteadOfBecomingMathematicalOrGovernance()
    {
        var fixture = CandidateFixture();
        const string path = "D5/X_Frontier/Unclassified.lean";
        fixture.Files[path] = "def unclassified : Unit := ()\n";
        fixture.Reports[path] = EmptyReport();

        var result = Run(fixture);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Contains("unclassified Frontier", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void OwnerOverrideRejectsInvalidUtf8WithoutRewritingTheInput()
    {
        using var directory = new TemporaryDirectory();
        var problemPath = Path.Combine(directory.Path, "invalid-utf8.txt");
        File.WriteAllBytes(problemPath, [0xff]);

        var result = Run(CandidateFixture(), "--owner-override-file", problemPath);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Contains("strict UTF-8", result.Error, StringComparison.Ordinal);
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
                "sha256:" + new string('1', 64),
                unsupported,
                [],
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
        var duplicate = Run(
            CandidateFixture(),
            "--owner-override-file", "first",
            "--owner-override-file", "second");

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
        string repositoryRoot = "/repo",
        RawChangeSet? changes = null)
    {
        var entries = reverseSnapshotEntries
            ? fixture.Files.Reverse().Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value))
            : fixture.Files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value));
        var environment = new ProductionCliEnvironment(
            repositoryRoot,
            new FakeRepositoryGateway(
                changes ?? RawChangeSet.Create([]),
                RawRepositorySnapshot.Create(entries),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));
        return environment.TheoryCandidates(arguments ?? []);
    }

    private static (RepositorySnapshot Snapshot, TruthDagProjection Dag) Truth(RuleFixture fixture)
    {
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(fixture.Files.Select(static pair =>
                RawRepositoryEntry.FromText(pair.Key, pair.Value))))).Snapshot;
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(LeanClosureValidator.Validate(
            snapshot,
            LeanAxiomReport.Create(fixture.Reports))).Capability;
        var dag = TruthDagProjectionAssembler.Build(snapshot, lean);
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
                "D5/X_Frontier/FrontierMathematicalOpen",
                StringComparison.Ordinal);
        fixture.Files[MissionFileLoader.RelativePath] = FixtureMission;
        fixture.Files[MathematicalFrontierPath] =
            "/-- TASK D5-T0099\n"
            + "    Prove every norm-unit is plus or minus an integral phi power, then derive Euclidean or PID structure. -/\n"
            + "def goldenUnitsPrincipalIdealDelivery : Unit := ()\n";
        fixture.Files[GovernanceFrontierPath] =
            "/- TASK D5-T0100\n    Harness work item. -/\ndef governanceTicket : Unit := ()\n";
        fixture.Files[DeclarationReadyFrontierPath] =
            "theorem o5_independence : True := by sorry\n"
            + "def o6WeilPositivityStatement : Prop := True\n"
            + "def supportValue : Nat := 0\n";
        fixture.Files[NonFrontierOpenPath] = "theorem unfinishedFact : True := by sorry\n";
        fixture.Reports[MathematicalFrontierPath] = EmptyReport();
        fixture.Reports[GovernanceFrontierPath] = EmptyReport();
        fixture.Reports[DeclarationReadyFrontierPath] = new LeanFileReport(
            [],
            [
                new LeanDeclaration(
                    "D5.X_Frontier.Hearts.o5_independence",
                    "theorem",
                    "statement-v1(uparams=[],type=ec(ns(n0,4:True),[]))",
                    ["sorryAx"]),
                new LeanDeclaration(
                    "D5.X_Frontier.Hearts.o6WeilPositivityStatement",
                    "def",
                    "statement-v1(uparams=[],type=es(l0),value=ec(ns(n0,4:True),[]))",
                    []),
                new LeanDeclaration(
                    "D5.X_Frontier.Hearts.supportValue",
                    "def",
                    "statement-v1(uparams=[],type=ec(ns(n0,3:Nat),[]),value=ei(ln(0)))",
                    []),
            ]);
        fixture.Reports[NonFrontierOpenPath] = new LeanFileReport(
            [],
            [new LeanDeclaration("unfinishedFact", "theorem", "True", ["sorryAx"])]);
        return fixture;
    }

    private static RuleFixture CandidateFixtureWithMismatchedProjectedStatus()
    {
        const string mismatchedPath =
            "Meta/Digestion/backfill/fixture-source/absorbed-closed/fixture-atom.yaml";
        var fixture = CandidateFixture();
        var atom = fixture.Files[ResidualAtomPath];
        fixture.Files.Remove(ResidualAtomPath);
        fixture.Files[mismatchedPath] = atom;
        return fixture;
    }

    private static RuleFixture CandidateFixtureWithNoncanonicalSourceMetadata()
    {
        var fixture = CandidateFixture();
        fixture.Files[RuleFixture.FixtureBackfillSourcePath] += "\n";
        return fixture;
    }

    private static LeanFileReport EmptyReport() => new([], []);

}
