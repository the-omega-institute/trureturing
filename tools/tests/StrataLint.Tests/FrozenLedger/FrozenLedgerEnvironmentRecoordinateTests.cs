using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    private const string RecoordinateSource = "theorem a : True := by trivial\n";
    private const string UnprovedEquivalence = "representation-migration; equivalence-unproved";

    [Fact]
    public void LedgerWithoutEnvironmentRecoordinateRetainsExactBytesAndBehavior()
    {
        var catalog = BuildCatalog(Module("A"));
        var bytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var syntax = LoadedEnvironmentLedger(bytes.AsSpan());

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
        IEnumerable<string>? candidateDeclarations = null)
    {
        var baselineCatalog = BuildCatalog(ModuleWithReport(
            "A",
            RecoordinateSource,
            "old-elaborated-expression",
            baselineAxioms,
            new[] { "a" }));
        var candidateCatalog = BuildCatalog(ModuleWithReport(
            "A",
            candidateSource,
            "new-elaborated-expression",
            candidateAxioms ?? baselineAxioms,
            candidateDeclarations ?? new[] { "a" }));
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
        var sourceBlob = fixture.BaselineNode.Attestation.SourceBlobOid;
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
                ["new"] = EnvironmentPins('4', '5', '6'),
                ["old"] = EnvironmentPins('1', '2', '3'),
            },
            ["equivalence_status"] = UnprovedEquivalence,
            ["kernel_verdict"] = nameof(TruthState.Closed),
            ["new_axiom_closure"] = new JsonArray(
                fixture.CandidateNode.AxiomClosure.Select(static item => JsonValue.Create(item)).ToArray()),
            ["new_input"] = Input(
                fixture.CandidateNode,
                GitOid('c'),
                GitOid('d'),
                sourceBlob,
                new[] { GitOid('4'), GitOid('5'), GitOid('6') }),
            ["new_statement_id"] = fixture.CandidateNode.StatementId.Value,
            ["old_axiom_closure"] = new JsonArray(
                fixture.BaselineNode.AxiomClosure.Select(static item => JsonValue.Create(item)).ToArray()),
            ["old_input"] = Input(
                fixture.BaselineNode,
                GitOid('a'),
                GitOid('b'),
                sourceBlob,
                new[] { GitOid('1'), GitOid('2'), GitOid('3') }),
            ["old_statement_id"] = fixture.BaselineNode.StatementId.Value,
            ["previous_attestation_event_hash"] = freeze.EventHash,
        };
    }

    private static JsonObject EnvironmentPins(char toolchain, char lakefile, char manifest) => new()
    {
        ["lake_manifest_blob_oid"] = GitOid(manifest),
        ["lakefile_blob_oid"] = GitOid(lakefile),
        ["lakefile_path"] = "lakefile.toml",
        ["lean_toolchain_blob_oid"] = GitOid(toolchain),
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
