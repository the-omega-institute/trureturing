using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    private const string SupersedeSource = "theorem a : True := by trivial\n";

    [Fact]
    public void SupersedePayloadContainsOnlyFreshCoordinateAndChainFields()
    {
        var fixture = SupersedeFixture();
        var payload = SupersedePayload(fixture);
        var element = FrozenLedgerCanonicalWriter.SupersedeElement(payload);

        Assert.Equal(
            new[]
            {
                "axiom_closure",
                "case_id",
                "declaration_statement_ids",
                "environment",
                "frozen_node_id",
                "input",
                "prerequisite_frozen_node_ids",
                "previous_attestation_event_hash",
                "statement_id",
                "witness_id",
            },
            element.EnumerateObject().Select(static property => property.Name).ToArray());
        Assert.DoesNotContain(
            element.EnumerateObject(),
            static property => property.Name.StartsWith("old_", StringComparison.Ordinal));
    }

    [Fact]
    public void SupersedeAcceptsSameTheoremAndSmallerClosureAndMarksOldNodeSuperseded()
    {
        var fixture = SupersedeFixture(
            baselineAxioms: ["Classical.choice", "propext"],
            candidateAxioms: ["propext"]);

        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateCandidate(
                LoadedSupersedeLedger(AppendSupersede(fixture).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog)).Capability;

        Assert.IsType<FrozenLedgerEvent.Supersede>(accepted.Events[^1]);
        Assert.Equal(fixture.CandidateNode.FrozenNodeId, accepted.ActiveFrozenNodes.Single().FrozenNodeId);
        Assert.Contains(fixture.BaselineNode.FrozenNodeId, accepted.SupersededFrozenNodeIds);
        Assert.DoesNotContain(fixture.BaselineNode.FrozenNodeId, accepted.RevokedFrozenNodeIds);
    }

    [Fact]
    public void SupersedeRejectsLargerClosure()
    {
        var fixture = SupersedeFixture(
            baselineAxioms: ["propext"],
            candidateAxioms: ["Classical.choice", "propext"]);

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                LoadedSupersedeLedger(AppendSupersede(fixture).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog));

        Assert.Contains("axiom closure", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void SupersedeRejectsIncomparableClosure()
    {
        var fixture = SupersedeFixture(
            baselineAxioms: ["propext"],
            candidateAxioms: ["Classical.choice"]);

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                LoadedSupersedeLedger(AppendSupersede(fixture).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog));

        Assert.Contains("axiom closure", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void SupersedeAcceptsUnchangedSourceWithAmbientStatementDriftAndSmallerClosure()
    {
        var fixture = SupersedeFixture(
            baselineAxioms: ["Classical.choice", "propext"],
            candidateAxioms: ["propext"],
            candidateStatementMaterial: "ambiently-different-elaborated-expression");

        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateCandidate(
                LoadedSupersedeLedger(AppendSupersede(fixture).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog)).Capability;

        Assert.Equal(fixture.CandidateNode.FrozenNodeId, accepted.ActiveFrozenNodes.Single().FrozenNodeId);
        Assert.Contains(fixture.BaselineNode.FrozenNodeId, accepted.SupersededFrozenNodeIds);
    }

    [Fact]
    public void SupersedeRejectsChangedSourceAndStatementEvenWhenClosureShrinks()
    {
        var fixture = SupersedeFixture(
            baselineAxioms: ["Classical.choice", "propext"],
            candidateAxioms: ["propext"],
            baselineSource: "theorem a : True /\\ True := by simp\n",
            candidateSource: SupersedeSource,
            baselineStatementMaterial: "And True True",
            candidateStatementMaterial: "True");

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                LoadedSupersedeLedger(AppendSupersede(fixture).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog));

        Assert.Contains("source blob", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void SupersedeRejectsChangedIncludedDeclarationKeyWithUnchangedSource()
    {
        var fixture = SupersedeFixture(
            baselineDeclarations: ["a"],
            candidateDeclarations: ["renamed"],
            candidateStatementMaterial: "ambiently-different-elaborated-expression");

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                LoadedSupersedeLedger(AppendSupersede(fixture).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog));

        Assert.Contains("declaration keys", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void SupersedeRejectsStatementDriftWhenSupportingBlobOidsAreUnchanged()
    {
        var fixture = SupersedeFixture(
            candidateStatementMaterial: "ambiently-different-elaborated-expression");
        var payload = SupersedePayload(fixture);
        var baseEntry = Assert.Single(fixture.Baseline.ActiveEntries).Value;
        var unchangedPinsEntry = baseEntry with
        {
            Payload = baseEntry.Payload with
            {
                Input = baseEntry.Payload.Input with
                {
                    SupportingBlobOids = payload.Input.SupportingBlobOids,
                },
            },
        };

        var exception = Assert.Throws<FormatException>(() =>
            FrozenLedger.ValidateSupersedeStrength(payload, unchangedPinsEntry));

        Assert.Contains("environment pins did not change", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void SupersedeRejectsFreshCoordinateThatDoesNotMatchCandidateReport()
    {
        var fixture = SupersedeFixture();
        var payload = SupersedePayload(fixture);
        var mismatched = FrozenLedgerCanonicalWriter.SupersedeElement(payload);
        var mutable = JsonNode.Parse(mismatched.GetRawText())!.AsObject();
        mutable["witness_id"] = Sha256("not-the-candidate-witness");

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                LoadedSupersedeLedger(AppendSupersede(fixture, mutable).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog));

        Assert.Contains("candidate Closed material", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void SupersedeDagOrdersChangedPrerequisiteBeforeItsDependent()
    {
        var oldPrerequisite = Sha256("old-prerequisite");
        var oldDependent = Sha256("old-dependent");
        var newPrerequisite = Sha256("new-prerequisite");
        var newDependent = Sha256("new-dependent");
        var prerequisiteSupersedeHash = Sha256("prerequisite-supersede-event");
        var dependentSupersedeHash = Sha256("dependent-supersede-event");
        var prerequisiteSupersede = DagEvent(
            "z-prerequisite-supersede",
            prerequisiteSupersedeHash,
            FrozenLedger.SupersedeEventType,
            new
            {
                frozen_node_id = newPrerequisite,
                prerequisite_frozen_node_ids = Array.Empty<string>(),
                previous_attestation_event_hash = Sha256("prerequisite-freeze-event"),
            });
        var dependentSupersede = DagEvent(
            "a-dependent-supersede",
            dependentSupersedeHash,
            FrozenLedger.SupersedeEventType,
            new
            {
                frozen_node_id = newDependent,
                prerequisite_frozen_node_ids = new[] { newPrerequisite },
                previous_attestation_event_hash = Sha256("dependent-freeze-event"),
            });
        var events = ImmutableArray.Create(
            DagEvent("genesis", Sha256("genesis-event"), "Genesis", new { }),
            DagEvent(
                oldPrerequisite,
                Sha256("prerequisite-freeze-event"),
                "Freeze",
                new { prerequisite_frozen_node_ids = Array.Empty<string>() }),
            DagEvent(
                oldDependent,
                Sha256("dependent-freeze-event"),
                "Freeze",
                new { prerequisite_frozen_node_ids = new[] { oldPrerequisite } }),
            dependentSupersede,
            prerequisiteSupersede);

        Assert.True(DagLedgerLoader.TryOrderClosedDag(events, [], out var ordered));

        Assert.True(
            ordered.IndexOf(prerequisiteSupersede) < ordered.IndexOf(dependentSupersede),
            "The fresh prerequisite node identity must be placed before a Supersede that depends on it.");
    }

    [Fact]
    public void RevokeTargetsTheCurrentSupersedeNodeRatherThanItsFileIdentity()
    {
        var freezeHash = Sha256("freeze-event");
        var currentNodeId = FrozenNodeId.Create(Sha256("current-supersede-node"));
        var supersede = new TrustedFrozenLedgerEvent(
            RepoPath.CreateKnown("Golden/Frozen/accepted/supersede.json"),
            FrozenLedger.SupersedeEventType,
            Sha256("supersede-event"),
            Sha256("supersede-file-identity"),
            JsonSerializer.SerializeToElement(new
            {
                frozen_node_id = currentNodeId.Value,
                previous_attestation_event_hash = freezeHash,
            }));
        var events = ImmutableArray.Create(
            new TrustedFrozenLedgerEvent(
                RepoPath.CreateKnown("Golden/Frozen/accepted/freeze.json"),
                "Freeze",
                freezeHash,
                Sha256("old-node"),
                JsonSerializer.SerializeToElement(new { })),
            supersede,
            new TrustedFrozenLedgerEvent(
                RepoPath.CreateKnown("Golden/Frozen/accepted/revoke.json"),
                "Revoke",
                Sha256("revoke-event"),
                Sha256("revoke-file-identity"),
                JsonSerializer.SerializeToElement(new
                {
                    affected_frozen_node_ids = new[] { currentNodeId.Value },
                })));

        Assert.Empty(FrozenLedgerAttestationChain.ActiveAttestations(events));
    }

    private static SupersedeTestFixture SupersedeFixture(
        IEnumerable<string>? baselineAxioms = null,
        IEnumerable<string>? candidateAxioms = null,
        string? baselineSource = null,
        string? candidateSource = null,
        string baselineStatementMaterial = "same-elaborated-expression",
        string candidateStatementMaterial = "same-elaborated-expression",
        IEnumerable<string>? baselineDeclarations = null,
        IEnumerable<string>? candidateDeclarations = null)
    {
        var protectedSource = baselineSource ?? SupersedeSource;
        var baselineCatalog = BuildCatalogWithEnvironment(
            "leanprover/lean4:v4.31.0\n",
            "[package]\nname = \"old\"\n",
            "{\"version\":\"old\"}\n",
            GitOid('a'),
            GitOid('b'),
            ModuleWithReport(
                "A",
                protectedSource,
                baselineStatementMaterial,
                baselineAxioms,
                baselineDeclarations ?? ["a"]));
        var candidateCatalog = BuildCatalogWithEnvironment(
            "leanprover/lean4:v4.33.0\n",
            "[package]\nname = \"new\"\n",
            "{\"version\":\"new\"}\n",
            GitOid('c'),
            GitOid('d'),
            ModuleWithReport(
                "A",
                candidateSource ?? protectedSource,
                candidateStatementMaterial,
                candidateAxioms ?? baselineAxioms,
                candidateDeclarations ?? baselineDeclarations ?? ["a"]));
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            baselineCatalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(LoadedSupersedeLedger(baselineBytes.AsSpan()), baselineCatalog)).Capability;
        return new SupersedeTestFixture(
            candidateCatalog,
            baselineBytes,
            baseline,
            baselineCatalog.ClosedNodes.Single(),
            candidateCatalog.ClosedNodes.Single());
    }

    private static ImmutableArray<byte> AppendSupersede(
        SupersedeTestFixture fixture,
        JsonObject? payload = null)
    {
        var line = FrozenLedgerCanonicalWriter.WriteEvent(
            FrozenLedger.SupersedeEventType,
            JsonSerializer.SerializeToElement(
                payload ?? JsonNode.Parse(
                    FrozenLedgerCanonicalWriter.SupersedeElement(
                        SupersedePayload(fixture)).GetRawText())!.AsObject()),
            fixture.Baseline.HeadHash,
            fixture.Baseline.Events.Length).Bytes;
        return fixture.BaselineBytes.AddRange(line);
    }

    private static FrozenSupersedePayload SupersedePayload(SupersedeTestFixture fixture)
    {
        var freeze = Assert.IsType<FrozenLedgerEvent.Freeze>(fixture.Baseline.Events[1]);
        var environment = fixture.CandidateCatalog.Environment;
        var pins = new FrozenEnvironmentPins(
            environment.LakeManifestBlobOid,
            environment.LakefileBlobOid!,
            RepoPath.CreateKnown(environment.LakefilePath!),
            environment.LeanToolchainBlobOid);
        var input = FrozenLedgerCanonicalWriter.FreezePayload(
            fixture.CandidateCatalog.Environment,
            fixture.CandidateNode).Input with
        {
            SupportingBlobOids = new[]
            {
                pins.LakeManifestBlobOid,
                pins.LakefileBlobOid,
                pins.LeanToolchainBlobOid,
            }.Order(StringComparer.Ordinal).ToImmutableArray(),
        };
        return new FrozenSupersedePayload(
            fixture.CandidateNode.AxiomClosure,
            freeze.Payload.CaseId,
            fixture.CandidateNode.DeclarationStatementIds,
            pins,
            fixture.CandidateNode.FrozenNodeId,
            input,
            fixture.CandidateNode.PrerequisiteFrozenNodeIds,
            freeze.EventHash,
            fixture.CandidateNode.StatementId,
            fixture.CandidateNode.WitnessId);
    }

    private static FrozenLedgerSyntax LoadedSupersedeLedger(ReadOnlySpan<byte> bytes) =>
        Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes)).Syntax;

    private static DagLedgerFileEvent DagEvent(
        string identity,
        string eventHash,
        string eventType,
        object payload) =>
        new(
            RepoPath.CreateKnown($"Meta/Ledger/accepted/{identity}.json"),
            identity,
            eventHash,
            eventType,
            JsonSerializer.SerializeToElement(payload),
            FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion,
            null!,
            null);

    private sealed record SupersedeTestFixture(
        FrozenMaterialCatalog CandidateCatalog,
        ImmutableArray<byte> BaselineBytes,
        FrozenLedgerConsistent Baseline,
        FrozenNodeMaterial BaselineNode,
        FrozenNodeMaterial CandidateNode);
}
