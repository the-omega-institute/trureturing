using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class FrozenLedgerBaseViewTests
{
    private const string ModulePath = "D5/S0/Carrier/Ring.lean";
    private const string FrozenId =
        "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";

    [Fact]
    public void ProtectedBaseProjectionReadsPersistedStateWithoutRevalidatingAcceptedBytes()
    {
        var snapshot = Snapshot(TrustedButNoncanonicalBaseFiles());
        var oldValidator = FrozenAcceptedEventLoader.LoadFiles(snapshot.Files.Values.Where(file =>
            FrozenLedgerChangeClassifier.IsAcceptedEventPath(file.Path.Value)));

        Assert.IsType<DagLedgerFilesLoadOutcome.Invalid>(oldValidator);

        var view = FrozenLedgerBaseViewReader.Read(snapshot);

        var active = Assert.Single(view.ActiveByPath);
        Assert.Equal(ModulePath, active.Key.Value);
        Assert.Equal(FrozenId, active.Value.Material.FrozenNodeId.Value);
    }

    [Fact]
    public void ProtectedBaseProjectionRestoresRecordedAxiomClosure()
    {
        var view = FrozenLedgerBaseViewReader.Read(Snapshot(TrustedButNoncanonicalBaseFiles()));

        var active = Assert.Single(view.ActiveByPath).Value;
        Assert.True(active.AxiomClosureKnown);
        Assert.Equal(new[] { "Classical.choice" }, active.Material.AxiomClosure);
    }

    [Fact]
    public void AcceptedLoaderDecodesExistingV2Corpus()
    {
        var root = TestRepositoryLayout.FindRoot();
        var raw = new GitRepositoryGateway(root).ReadRevision("origin/dev");
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(raw)).Snapshot;
        var acceptedFiles = snapshot.Files.Values.Where(file =>
            FrozenLedgerChangeClassifier.IsAcceptedEventPath(file.Path.Value));

        var loaded = Assert.IsType<DagLedgerFilesLoadOutcome.Loaded>(
            FrozenAcceptedEventLoader.LoadFiles(acceptedFiles));

        Assert.NotEmpty(loaded.Events);

        // The corpus is mixed by design: 2 is the legacy encoding and
        // CurrentDagSchemaVersion is what the writer emits now, so pinning the whole
        // corpus to one version contradicts NewContentAddressedEventsUseSchemaV3 the
        // moment a new event lands. Pin the supported set that
        // FrozenLedgerCanonicalWriter already owns, and keep the legacy decode path
        // covered by requiring the v2 subset to stay non-empty.
        Assert.All(
            loaded.Events,
            static item => Assert.True(
                item.SchemaVersion is 2 or FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion,
                $"unsupported schema_version {item.SchemaVersion}"));
        Assert.Contains(loaded.Events, static item => item.SchemaVersion == 2);
    }

    [Fact]
    public void NewContentAddressedEventsUseSchemaV3()
    {
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Genesis",
            JsonSerializer.SerializeToElement(new
            {
                generator_blob_oid = FrozenLedgerTestData.GitOid('1'),
                origin_commit_oid = FrozenLedgerTestData.GitOid('2'),
                origin_tree_oid = FrozenLedgerTestData.GitOid('3'),
                protocol_version = 1,
                rule_catalog_root = RuleCatalog.Default.RootSha256,
            }));
        using var document = JsonDocument.Parse(encoded.Bytes.AsSpan()[..^1].ToArray());

        Assert.Equal(3, document.RootElement.GetProperty("schema_version").GetInt32());
    }

    [Fact]
    public void CurrentDevAcceptedSetProjectsWithoutAFindingOrVerdictObject()
    {
        var root = TestRepositoryLayout.FindRoot();
        var raw = new GitRepositoryGateway(root).ReadRevision("origin/dev");
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(raw)).Snapshot;

        var view = FrozenLedgerBaseViewReader.Read(snapshot);

        Assert.NotEmpty(view.ActiveByPath);
        Assert.Equal(
            snapshot.Files.Count(item =>
                FrozenLedgerChangeClassifier.IsAcceptedEventPath(item.Key.Value)),
            view.EventCount);
    }

    private static RepositorySnapshot Snapshot(IReadOnlyDictionary<string, string> files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(files.Select(pair =>
                RawRepositoryEntry.FromText(pair.Key, pair.Value))))).Snapshot;

    private static IReadOnlyDictionary<string, string> TrustedButNoncanonicalBaseFiles()
    {
        var genesis = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Genesis",
            JsonSerializer.SerializeToElement(new
            {
                generator_blob_oid = FrozenLedgerTestData.GitOid('1'),
                origin_commit_oid = FrozenLedgerTestData.GitOid('2'),
                origin_tree_oid = FrozenLedgerTestData.GitOid('3'),
                protocol_version = 1,
                rule_catalog_root = RuleCatalog.Default.RootSha256,
            }));
        var freeze = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Freeze",
            JsonSerializer.SerializeToElement(new
            {
                axiom_closure = new[] { "Classical.choice" },
                case_class = "active-frozen",
                case_id = "persisted-case-id",
                declaration_statement_ids = Array.Empty<object>(),
                evaluation = "admission",
                expected = new
                {
                    allowed_dispositions = new[] { "admit" },
                    diagnostic_match = "none",
                    required_diagnostics = Array.Empty<object>(),
                },
                frozen_node_id = FrozenId,
                input = new
                {
                    base_commit_oid = FrozenLedgerTestData.GitOid('4'),
                    base_tree_oid = FrozenLedgerTestData.GitOid('5'),
                    descriptor_blob_oid = FrozenLedgerTestData.GitOid('6'),
                    descriptor_selector = ModulePath,
                    materializer = "repository-snapshot-v1",
                    supporting_blob_oids = Array.Empty<string>(),
                },
                input_fingerprint = "persisted-witness-id",
                node_path = ModulePath,
                prerequisite_frozen_node_ids = Array.Empty<string>(),
                semantic_receipt = "persisted-semantic-receipt",
                statement_id = "persisted-statement-id",
                truth_state = "Closed",
                witness_id = "persisted-witness-id",
            }));
        var noncanonicalFreeze = "  " + Encoding.UTF8.GetString(freeze.Bytes.AsSpan()).TrimEnd() + "\n";
        return new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [FrozenLedgerChangeClassifier.AcceptedRoot + "/genesis-with-untrusted-name.json"] =
                Encoding.UTF8.GetString(genesis.Bytes.AsSpan()),
            [FrozenLedgerChangeClassifier.AcceptedRoot + "/freeze-with-untrusted-name.json"] =
                noncanonicalFreeze,
        };
    }
}
