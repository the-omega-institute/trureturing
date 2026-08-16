using System.Collections.Immutable;
using System.Reflection;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    private const string RecoordinateSource = "theorem a : True := by trivial\n";

    [Fact]
    public void RetiredEnvironmentRecoordinateProducerHelpersRemainAbsent()
    {
        const BindingFlags staticMethods = BindingFlags.Static | BindingFlags.NonPublic;

        Assert.Null(typeof(FrozenLedger).GetMethod(
            string.Concat("ValidateHistoryForEnvironment", "Recoordinate"),
            staticMethods));
        Assert.DoesNotContain(
            typeof(FrozenLedger).GetMethods(staticMethods).SelectMany(static method => method.GetParameters()),
            static parameter => parameter.Name == string.Concat("allowPendingEnvironment", "Recoordinate"));
        Assert.Null(typeof(DagLedgerCommandPreparation).GetMethod(
            string.Concat("Environment", "Pins"),
            staticMethods));
    }

    internal static (string Path, string Contents) EnvironmentRecoordinateDagEvent()
    {
        var payload = JsonSerializer.SerializeToElement(EnvironmentPayload(EnvironmentFixture()));
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
            FrozenLedger.EnvironmentRecoordinateEventType,
            payload);
        var identity = FrozenLedgerCanonicalWriter.EventIdentity(
            FrozenLedger.EnvironmentRecoordinateEventType,
            payload,
            encoded.Hash);
        return (
            $"{FrozenLedgerChangeClassifier.AcceptedRoot}/{identity[7..]}.json",
            System.Text.Encoding.UTF8.GetString(encoded.Bytes.AsSpan()));
    }
    private const string UnprovedEquivalence = "representation-migration; equivalence-unproved";

    [Fact]
    public void LedgerWithoutEnvironmentRecoordinateRetainsExactBytesAndBehavior()
    {
        var catalog = BuildCatalog(Module("A"));
        var bytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var syntax = LoadedEnvironmentLedger(bytes.AsSpan());

        Assert.Equal(
            "7f82664d7cfe5e8df1cf7b6fcf67f306f71e1df1b16ba0851bfb31913583b4e5",
            Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(bytes.AsSpan())));

        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(syntax, catalog)).Capability;

        Assert.True(accepted.RawBytes.AsSpan().SequenceEqual(bytes.AsSpan()));
        Assert.Equal(2, accepted.Events.Length);
        Assert.IsType<FrozenLedgerEvent.Genesis>(accepted.Events[0]);
        Assert.IsType<FrozenLedgerEvent.Freeze>(accepted.Events[1]);
    }

    [Fact]
    public void EnvironmentRecoordinateAcceptsEqualSourceStableDeclarationsAndNonexpandingAxioms()
    {
        var fixture = EnvironmentFixture();
        var candidate = AppendEnvironmentEvent(fixture);

        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateCandidate(LoadedEnvironmentLedger(candidate.AsSpan()), fixture.Baseline, fixture.CandidateCatalog)).Capability;
        var history = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(LoadedEnvironmentLedger(candidate.AsSpan()), fixture.CandidateCatalog)).Capability;

        Assert.True(candidate.AsSpan().StartsWith(fixture.BaselineBytes.AsSpan()));
        Assert.Equal("EnvironmentRecoordinate", accepted.Events[^1].GetType().Name);
        Assert.Equal(fixture.CandidateNode.StatementId, history.ActiveFrozenNodes.Single().StatementId);
    }

    [Fact]
    public void EnvironmentRecoordinateAcceptsEnvironmentChangeWithoutStatementDrift()
    {
        var fixture = EnvironmentFixture(candidateStatementMaterial: "old-elaborated-expression");
        Assert.Equal(fixture.BaselineNode.StatementId, fixture.CandidateNode.StatementId);

        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateCandidate(
                LoadedEnvironmentLedger(AppendEnvironmentEvent(fixture).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog)).Capability;

        Assert.IsType<FrozenLedgerEvent.EnvironmentRecoordinate>(accepted.Events[^1]);
        Assert.NotEqual(
            fixture.BaselineNode.WitnessId,
            accepted.ActiveFrozenNodes.Single().WitnessId);
    }

    [Fact]
    public void EnvironmentRecoordinateRejectsUnchangedEnvironmentWithoutStatementDrift()
    {
        var fixture = EnvironmentFixture(
            candidateStatementMaterial: "old-elaborated-expression",
            reuseBaselineEnvironment: true);
        Assert.Equal(fixture.BaselineNode.StatementId, fixture.CandidateNode.StatementId);

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                LoadedEnvironmentLedger(AppendEnvironmentEvent(fixture).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog));

        Assert.Contains("environment", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void EnvironmentRecoordinateRejectsDifferentSourceBlob()
    {
        var fixture = EnvironmentFixture(candidateSource: RecoordinateSource + "-- changed\n");

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                LoadedEnvironmentLedger(AppendEnvironmentEvent(fixture).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog));

        Assert.Contains("source", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void EnvironmentRecoordinateRejectsChangedDeclarationSet()
    {
        var fixture = EnvironmentFixture(candidateDeclarations: new[] { "a", "b" });

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                LoadedEnvironmentLedger(AppendEnvironmentEvent(fixture).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog));

        Assert.Contains("declaration", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void EnvironmentRecoordinateRejectsAxiomClosureExpansion()
    {
        var fixture = EnvironmentFixture(
            baselineAxioms: new[] { "propext" },
            candidateAxioms: new[] { "propext", "Classical.choice" });

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                LoadedEnvironmentLedger(AppendEnvironmentEvent(fixture).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog));

        Assert.Contains("axiom", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void EnvironmentRecoordinateRejectsModuleStatementIdUnlinkedFromDeclarations()
    {
        var fixture = EnvironmentFixture();
        var payload = EnvironmentPayload(fixture);
        payload["new_statement_id"] = Sha256("unlinked-module-statement");

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                LoadedEnvironmentLedger(AppendEnvironmentEvent(fixture, payload).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog));

        Assert.Contains("declaration statement", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Theory]
    [InlineData("equivalence_status", false)]
    [InlineData("unexpected", true)]
    public void EnvironmentRecoordinateRejectsMissingOrUnknownFields(string field, bool add)
    {
        var fixture = EnvironmentFixture();
        var payload = EnvironmentPayload(fixture);
        if (add)
        {
            payload[field] = "forbidden";
        }
        else
        {
            payload.Remove(field);
        }

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                LoadedEnvironmentLedger(AppendEnvironmentEvent(fixture, payload).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog));

        Assert.Contains("field", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void EnvironmentRecoordinateRejectsMissingNestedEnvironmentPin()
    {
        var fixture = EnvironmentFixture();
        var payload = EnvironmentPayload(fixture);
        payload["environment"]!["new"]!.AsObject().Remove("lakefile_blob_oid");

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                LoadedEnvironmentLedger(AppendEnvironmentEvent(fixture, payload).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog));

        Assert.Contains("field", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void EnvironmentRecoordinateRejectsNestedUnknownField()
    {
        var fixture = EnvironmentFixture();
        var payload = EnvironmentPayload(fixture);
        payload["declaration_statement_ids"]!["old"]![0]!["unknown"] = "forbidden";

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                LoadedEnvironmentLedger(AppendEnvironmentEvent(fixture, payload).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog));

        Assert.Contains("field", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void EnvironmentRecoordinateRejectsWrongFieldType()
    {
        var fixture = EnvironmentFixture();
        var payload = EnvironmentPayload(fixture);
        payload["kernel_verdict"] = 1;

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                LoadedEnvironmentLedger(AppendEnvironmentEvent(fixture, payload).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog));

        Assert.Contains("string", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Theory]
    [InlineData("equivalence_status", "equivalence-proved")]
    [InlineData("kernel_verdict", "Open")]
    public void EnvironmentRecoordinateRejectsUnsupportedSemanticClaims(string field, string value)
    {
        var fixture = EnvironmentFixture();
        var payload = EnvironmentPayload(fixture);
        payload[field] = value;

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                LoadedEnvironmentLedger(AppendEnvironmentEvent(fixture, payload).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog));

        Assert.Contains(field == "equivalence_status" ? "equivalence" : "Closed",
            rejected.Message,
            StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void EnvironmentRecoordinateCannotCoverOrRewriteAnExistingFreeze()
    {
        var fixture = EnvironmentFixture();
        var payload = EnvironmentPayload(fixture);
        payload["case_id"] = "active-frozen/" + Sha256("not-active")[7..];

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                LoadedEnvironmentLedger(AppendEnvironmentEvent(fixture, payload).AsSpan()),
                fixture.Baseline,
                fixture.CandidateCatalog));

        Assert.Contains("active", rejected.Message, StringComparison.OrdinalIgnoreCase);
        Assert.IsType<FrozenLedgerEvent.Freeze>(fixture.Baseline.Events[1]);
    }

    private static EnvironmentRecoordinateFixture EnvironmentFixture(
        string candidateSource = RecoordinateSource,
        IEnumerable<string>? baselineAxioms = null,
        IEnumerable<string>? candidateAxioms = null,
        IEnumerable<string>? candidateDeclarations = null,
        string candidateStatementMaterial = "new-elaborated-expression",
        bool reuseBaselineEnvironment = false)
    {
        var baselineCatalog = BuildCatalogWithEnvironment(
            "leanprover/lean4:v4.31.0\n",
            "[package]\nname = \"old\"\n",
            "{\"version\":\"old\"}\n",
            GitOid('a'),
            GitOid('b'),
            ModuleWithReport(
                "A",
                RecoordinateSource,
                "old-elaborated-expression",
                baselineAxioms,
                new[] { "a" }));
        var candidateCatalog = BuildCatalogWithEnvironment(
            reuseBaselineEnvironment
                ? "leanprover/lean4:v4.31.0\n"
                : "leanprover/lean4:v4.33.0\n",
            reuseBaselineEnvironment
                ? "[package]\nname = \"old\"\n"
                : "[package]\nname = \"new\"\n",
            reuseBaselineEnvironment
                ? "{\"version\":\"old\"}\n"
                : "{\"version\":\"new\"}\n",
            GitOid('a'),
            GitOid('b'),
            ModuleWithReport(
                "A",
                candidateSource,
                candidateStatementMaterial,
                candidateAxioms ?? baselineAxioms,
                candidateDeclarations ?? new[] { "a" }) with
            {
                BaseCommitOid = GitOid('c'),
                BaseTreeOid = GitOid('d'),
            });
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            baselineCatalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(LoadedEnvironmentLedger(baselineBytes.AsSpan()), baselineCatalog)).Capability;
        return new EnvironmentRecoordinateFixture(
            baselineCatalog,
            candidateCatalog,
            baselineBytes,
            baseline,
            baselineCatalog.ClosedNodes.Single(),
            candidateCatalog.ClosedNodes.Single());
    }

    private static ImmutableArray<byte> AppendEnvironmentEvent(
        EnvironmentRecoordinateFixture fixture,
        JsonObject? payload = null)
    {
        var line = FrozenLedgerCanonicalWriter.WriteEvent(
            "EnvironmentRecoordinate",
            JsonSerializer.SerializeToElement(payload ?? EnvironmentPayload(fixture)),
            fixture.Baseline.HeadHash,
            fixture.Baseline.Events.Length).Bytes;
        return fixture.BaselineBytes.AddRange(line);
    }

    private static JsonObject EnvironmentPayload(EnvironmentRecoordinateFixture fixture)
    {
        var freeze = Assert.IsType<FrozenLedgerEvent.Freeze>(fixture.Baseline.Events[1]);
        return new JsonObject
        {
            ["case_id"] = freeze.Payload.CaseId,
            ["declaration_statement_ids"] = new JsonObject
            {
                ["new"] = DeclarationArray(fixture.CandidateNode),
                ["old"] = DeclarationArray(fixture.BaselineNode),
            },
            ["environment"] = new JsonObject
            {
                ["new"] = EnvironmentPins(fixture.CandidateCatalog.Environment),
                ["old"] = EnvironmentPins(fixture.BaselineCatalog.Environment),
            },
            ["equivalence_status"] = UnprovedEquivalence,
            ["kernel_verdict"] = nameof(TruthState.Closed),
            ["new_axiom_closure"] = new JsonArray(
                fixture.CandidateNode.AxiomClosure.Select(static item => JsonValue.Create(item)).ToArray()),
            ["new_frozen_node_id"] = fixture.CandidateNode.FrozenNodeId.Value,
            ["new_imports"] = new JsonArray(),
            ["new_input"] = Input(
                fixture.CandidateNode,
                fixture.CandidateNode.Attestation.BaseCommitOid
                    ?? fixture.CandidateCatalog.Environment.OriginCommitOid,
                fixture.CandidateNode.Attestation.BaseTreeOid
                    ?? fixture.CandidateCatalog.Environment.OriginTreeOid,
                fixture.CandidateNode.Attestation.SourceBlobOid,
                EnvironmentOidSet(fixture.CandidateCatalog.Environment)),
            ["new_statement_id"] = fixture.CandidateNode.StatementId.Value,
            ["new_prerequisite_frozen_node_ids"] = new JsonArray(
                fixture.CandidateNode.PrerequisiteFrozenNodeIds
                    .Select(static item => JsonValue.Create(item.Value)).ToArray()),
            ["new_witness_id"] = fixture.CandidateNode.WitnessId.Value,
            ["old_axiom_closure"] = new JsonArray(
                fixture.BaselineNode.AxiomClosure.Select(static item => JsonValue.Create(item)).ToArray()),
            ["old_frozen_node_id"] = fixture.BaselineNode.FrozenNodeId.Value,
            ["old_imports"] = new JsonArray(),
            ["old_input"] = Input(
                fixture.BaselineNode,
                fixture.BaselineNode.Attestation.BaseCommitOid
                    ?? fixture.BaselineCatalog.Environment.OriginCommitOid,
                fixture.BaselineNode.Attestation.BaseTreeOid
                    ?? fixture.BaselineCatalog.Environment.OriginTreeOid,
                fixture.BaselineNode.Attestation.SourceBlobOid,
                EnvironmentOidSet(fixture.BaselineCatalog.Environment)),
            ["old_statement_id"] = fixture.BaselineNode.StatementId.Value,
            ["old_prerequisite_frozen_node_ids"] = new JsonArray(
                fixture.BaselineNode.PrerequisiteFrozenNodeIds
                    .Select(static item => JsonValue.Create(item.Value)).ToArray()),
            ["old_witness_id"] = fixture.BaselineNode.WitnessId.Value,
            ["previous_attestation_event_hash"] = freeze.EventHash,
            ["source_sha256"] = Sha256Raw(RecoordinateSource),
        };
    }

    private static JsonObject EnvironmentPins(FrozenEnvironmentAttestation environment) => new()
    {
        ["lake_manifest_blob_oid"] = environment.LakeManifestBlobOid,
        ["lakefile_blob_oid"] = environment.LakefileBlobOid,
        ["lakefile_path"] = environment.LakefilePath,
        ["lean_toolchain_blob_oid"] = environment.LeanToolchainBlobOid,
    };

    private static JsonObject Input(
        FrozenNodeMaterial node,
        string commit,
        string tree,
        string sourceBlob,
        IEnumerable<string> pins) => new()
    {
        ["base_commit_oid"] = commit,
        ["base_tree_oid"] = tree,
        ["descriptor_blob_oid"] = sourceBlob,
        ["descriptor_selector"] = node.RepoPath.Value,
        ["materializer"] = "repository-snapshot-v1",
        ["supporting_blob_oids"] = new JsonArray(
            pins.Order(StringComparer.Ordinal).Select(static item => JsonValue.Create(item)).ToArray()),
    };

    private static JsonArray DeclarationArray(FrozenNodeMaterial node) => new(
        node.DeclarationStatementIds.Select(item => new JsonObject
        {
            ["declaration_name_key"] = item.DeclarationNameKey,
            ["kind"] = item.Kind,
            ["statement_id"] = item.StatementId.Value,
        }).ToArray());

    private static IEnumerable<string> EnvironmentOidSet(FrozenEnvironmentAttestation environment)
    {
        yield return environment.LakeManifestBlobOid;
        yield return environment.LakefileBlobOid!;
        yield return environment.LeanToolchainBlobOid;
    }

    private static string Sha256Raw(string value) =>
        "sha256:" + Convert.ToHexStringLower(
            System.Security.Cryptography.SHA256.HashData(System.Text.Encoding.UTF8.GetBytes(value)));

    private static FrozenLedgerSyntax LoadedEnvironmentLedger(ReadOnlySpan<byte> bytes) =>
        Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes)).Syntax;

    private sealed record EnvironmentRecoordinateFixture(
        FrozenMaterialCatalog BaselineCatalog,
        FrozenMaterialCatalog CandidateCatalog,
        ImmutableArray<byte> BaselineBytes,
        FrozenLedgerConsistent Baseline,
        FrozenNodeMaterial BaselineNode,
        FrozenNodeMaterial CandidateNode);
}
