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
    public void GenesisUsesItsPinnedSchemaV2()
    {
        var encoded = WriteGenesis();
        using var document = JsonDocument.Parse(encoded.Bytes.AsSpan()[..^1].ToArray());

        Assert.Equal(2, document.RootElement.GetProperty("schema_version").GetInt32());
    }

    [Fact]
    public void WriterBaselineReadsTrustedProjectionWithoutReplayingAcceptedEvents()
    {
        var view = FrozenLedgerBaseViewReader.Read(Snapshot(TrustedButNoncanonicalBaseFiles()));
        var root = TestRepositoryLayout.FindRoot();
        var raw = new GitRepositoryGateway(root).ReadCurrent();
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(raw)).Snapshot;
        var baseline = view.ToWriterBaseline();

        var source = snapshot.Files[RepoPath.CreateKnown(
            "tools/StrataLint.Engine/Ledger/Admission/FrozenLedgerBaseView.cs")].Text;

        Assert.Equal(view.EventCount, baseline.EventCount);
        Assert.Equal(view.ActiveByCase.Keys.Order(), baseline.ActiveEntries.Keys.Order());
        Assert.DoesNotContain("ToWriterSyntax", source, StringComparison.Ordinal);
        Assert.DoesNotContain(
            "FrozenLedgerCanonicalWriter.WriteEvent",
            source,
            StringComparison.Ordinal);
    }

    private static (ImmutableArray<byte> Bytes, string Hash) WriteGenesis() =>
        FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Genesis",
            JsonSerializer.SerializeToElement(new
            {
                generator_blob_oid = FrozenLedgerTestData.GitOid('1'),
                origin_commit_oid = FrozenLedgerTestData.GitOid('2'),
                origin_tree_oid = FrozenLedgerTestData.GitOid('3'),
                protocol_version = 1,
                rule_catalog_root = RuleCatalog.Default.RootSha256,
            }));

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
        var freeze = JsonSerializer.Serialize(new
        {
            event_hash = FrozenLedgerTestData.Sha256("trusted v3 freeze"),
            event_type = "Freeze",
            payload = new
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
                input_fingerprint = FrozenLedgerTestData.Sha256("trusted v3 input"),
                node_path = ModulePath,
                prerequisite_frozen_node_ids = Array.Empty<string>(),
                semantic_receipt = FrozenId,
                statement_id = "persisted-statement-id",
                truth_state = "Closed",
                witness_id = "persisted-witness-id",
            },
            schema_version = 3,
        });
        var noncanonicalFreeze = "  " + freeze + "\n";
        return new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [FrozenLedgerChangeClassifier.AcceptedRoot + "/genesis-with-untrusted-name.json"] =
                Encoding.UTF8.GetString(genesis.Bytes.AsSpan()),
            [FrozenLedgerChangeClassifier.AcceptedRoot + "/freeze-with-untrusted-name.json"] =
                noncanonicalFreeze,
        };
    }
}
