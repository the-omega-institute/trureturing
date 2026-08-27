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
    private const string ExistingV2FrozenId =
        "sha256:b69ef8a20199cf6db2c1bd00805a700b808951a1cb4901f91b9cfbe1ef3f4f92";
    private const string ExistingV2NodePath = "D5/S3/Weil/ZetaCore/InstancePriorities.lean";
    private const string ExistingV2Fixture =
        "{\"event_hash\": \"sha256:fa3d4d56bec87d3af21b3f88c0688eae217a0903f6f7fa20b53c4925d7338603\", \"event_type\": \"Freeze\", \"payload\": {\"case_class\": \"active-frozen\", \"case_id\": \"active-frozen/b69ef8a20199cf6db2c1bd00805a700b808951a1cb4901f91b9cfbe1ef3f4f92\", \"declaration_statement_ids\": [], \"evaluation\": \"admission\", \"expected\": {\"allowed_dispositions\": [\"admit\"], \"diagnostic_match\": \"none\", \"required_diagnostics\": []}, \"frozen_node_id\": \"sha256:b69ef8a20199cf6db2c1bd00805a700b808951a1cb4901f91b9cfbe1ef3f4f92\", \"input\": {\"base_commit_oid\": \"git-sha1:037b3e339009f9ccafc2b51aaaeef1a3e6244876\", \"base_tree_oid\": \"git-sha1:20d38fef8eff7bdb111ed9fdc9b8e2ddf83e06f9\", \"descriptor_blob_oid\": \"git-sha1:cccbf4dae4bb3f39fe075a26c22d12627b690622\", \"descriptor_selector\": \"D5/S3/Weil/ZetaCore/InstancePriorities.lean\", \"materializer\": \"repository-snapshot-v1\", \"supporting_blob_oids\": [\"git-sha1:1123096aedfa69a2db94d58b957a45f8dc0cc006\", \"git-sha1:18640c8b066b182147f324d3aefd8ee48ee45238\"]}, \"input_fingerprint\": \"sha256:bbca9be5f7d9e8102631e860373767b9945319f5961d2ef647e72c786d2afe35\", \"node_path\": \"D5/S3/Weil/ZetaCore/InstancePriorities.lean\", \"prerequisite_frozen_node_ids\": [], \"semantic_receipt\": \"sha256:b69ef8a20199cf6db2c1bd00805a700b808951a1cb4901f91b9cfbe1ef3f4f92\", \"statement_id\": \"sha256:7ccc628c8a8d63c828e5b5dbc87fb1dff2b5a1111cf8ed2e5bcce27f211e7836\", \"truth_state\": \"Closed\", \"witness_id\": \"sha256:bbca9be5f7d9e8102631e860373767b9945319f5961d2ef647e72c786d2afe35\"}, \"schema_version\": 2}\n";

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
        var v2Only = ExistingV2FixtureFiles();
        var loadedV2Only = LoadAccepted(v2Only);

        Assert.DoesNotContain(loadedV2Only.Events, static item => item.SchemaVersion == 3);
        AssertExistingV2Freeze(Assert.Single(loadedV2Only.Events));

        var v3Genesis = WriteGenesis(schemaVersion: 3);
        var withV3 = new Dictionary<string, string>(v2Only, StringComparer.Ordinal)
        {
            [FrozenLedgerChangeClassifier.AcceptedPath(v3Genesis.Hash)] =
                Encoding.UTF8.GetString(v3Genesis.Bytes.AsSpan()),
        };
        var loadedWithV3 = LoadAccepted(withV3);

        Assert.Contains(loadedWithV3.Events, static item => item.SchemaVersion == 3);
        AssertExistingV2Freeze(Assert.Single(
            loadedWithV3.Events.Where(static item => item.Identity == ExistingV2FrozenId)));
    }

    [Fact]
    public void NewContentAddressedEventsUseSchemaV4()
    {
        var encoded = WriteGenesis();
        using var document = JsonDocument.Parse(encoded.Bytes.AsSpan()[..^1].ToArray());

        Assert.Equal(4, document.RootElement.GetProperty("schema_version").GetInt32());
    }

    [Fact]
    public void CurrentDevAcceptedSetProjectsWithoutAFindingOrVerdictObject()
    {
        var root = TestRepositoryLayout.FindRoot();
        var raw = new GitRepositoryGateway(root).ReadCurrent();
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(raw)).Snapshot;

        var view = FrozenLedgerBaseViewReader.Read(snapshot);

        Assert.NotEmpty(view.ActiveByPath);
        Assert.Equal(
            snapshot.Files.Count(item =>
                FrozenLedgerChangeClassifier.IsAcceptedEventPath(item.Key.Value)),
            view.EventCount);
        var source = snapshot.Files[RepoPath.CreateKnown(
            "tools/StrataLint.Engine/Ledger/Admission/FrozenLedgerBaseView.cs")].Text;
        Assert.DoesNotContain("FrozenLedger.ApplyReattest", source, StringComparison.Ordinal);
        Assert.DoesNotContain("FrozenLedger.ApplySupersede", source, StringComparison.Ordinal);
        var preparation = snapshot.Files[RepoPath.CreateKnown(
            "tools/StrataLint.Cli/Commands/Ledger/DagLedgerCommandPreparation.cs")].Text;
        Assert.DoesNotContain("FrozenLedger.ValidateHistoryPrefix", preparation, StringComparison.Ordinal);
        Assert.DoesNotContain("FrozenLedger.ScanReferences", preparation, StringComparison.Ordinal);
    }

    [Fact]
    public void WriterBaselineReadsTrustedProjectionWithoutReplayingAcceptedEvents()
    {
        var root = TestRepositoryLayout.FindRoot();
        var raw = new GitRepositoryGateway(root).ReadCurrent();
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(raw)).Snapshot;
        var view = FrozenLedgerBaseViewReader.Read(snapshot);
        var baseline = view.ToWriterBaseline();

        var source = snapshot.Files[RepoPath.CreateKnown(
            "tools/StrataLint.Engine/Ledger/Admission/FrozenLedgerBaseView.cs")].Text;
        Assert.Equal(view.EventCount, baseline.Events.Length);
        Assert.Equal(view.ActiveByCase.Keys.Order(), baseline.ActiveEntries.Keys.Order());
        Assert.DoesNotContain("ToWriterSyntax", source, StringComparison.Ordinal);
        Assert.DoesNotContain(
            "FrozenLedgerCanonicalWriter.WriteEvent",
            source,
            StringComparison.Ordinal);
    }

    [Fact]
    public void BaseProjectionConsumesHistoricalLegacyReattestBeforeRevoke()
    {
        var view = FrozenLedgerBaseViewReader.Read(Snapshot(
            ReattestedThenRevokedFiles(ReattestShape.HistoricalLegacy)));

        Assert.Empty(view.ActiveByCase);
    }

    [Fact]
    public void BaseProjectionConsumesSchemaV4LegacyReattestBeforeRevoke()
    {
        var view = FrozenLedgerBaseViewReader.Read(Snapshot(
            ReattestedThenRevokedFiles(ReattestShape.SchemaV4Legacy)));

        Assert.Empty(view.ActiveByCase);
    }

    [Fact]
    public void BaseProjectionConsumesSchemaV4ExtendedReattestBeforeRevoke()
    {
        var view = FrozenLedgerBaseViewReader.Read(Snapshot(
            ReattestedThenRevokedFiles(ReattestShape.SchemaV4Extended)));

        Assert.Empty(view.ActiveByCase);
    }

    private static DagLedgerFilesLoadOutcome.Loaded LoadAccepted(
        IReadOnlyDictionary<string, string> files)
    {
        var acceptedFiles = Snapshot(files).Files.Values.Where(file =>
            FrozenLedgerChangeClassifier.IsAcceptedEventPath(file.Path.Value));
        return Assert.IsType<DagLedgerFilesLoadOutcome.Loaded>(
            FrozenAcceptedEventLoader.LoadFiles(acceptedFiles));
    }

    private static Dictionary<string, string> ExistingV2FixtureFiles() =>
        new(StringComparer.Ordinal)
        {
            [FrozenLedgerChangeClassifier.AcceptedPath(ExistingV2FrozenId)] = ExistingV2Fixture,
        };

    private static void AssertExistingV2Freeze(DagLedgerFileEvent item)
    {
        Assert.Equal(ExistingV2FrozenId, item.Identity);
        Assert.Equal("Freeze", item.EventType);
        Assert.Equal(2, item.SchemaVersion);
        Assert.Equal(ExistingV2FrozenId, item.Payload.GetProperty("frozen_node_id").GetString());
        Assert.Equal(ExistingV2NodePath, Assert.IsType<FrozenLedgerInput>(item.Input).DescriptorSelector);
    }

    private static IReadOnlyDictionary<string, string> ReattestedThenRevokedFiles(
        ReattestShape shape)
    {
        var catalog = FrozenLedgerTestData.BuildCatalog(FrozenLedgerTestData.Module("A"));
        var generated = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(FrozenLedgerTestData.GitOid('e'), RuleCatalog.Default.RootSha256));
        var files = new Dictionary<string, string>(StringComparer.Ordinal);
        FrozenLedgerTestData.AddLedgerFiles(files, generated);
        var frozen = Assert.Single(FrozenLedgerBaseViewReader.Read(Snapshot(files)).ActiveByCase).Value;
        var freshNodeId = "sha256:" + new string('b', 64);
        var input = frozen.Payload.Input;
        var inputElement = new
        {
            base_commit_oid = input.BaseCommitOid,
            base_tree_oid = input.BaseTreeOid,
            descriptor_blob_oid = input.DescriptorBlobOid,
            descriptor_selector = input.DescriptorSelector,
            materializer = input.Materializer,
            supporting_blob_oids = input.SupportingBlobOids,
        };
        var reattestPayload = shape switch
        {
            ReattestShape.HistoricalLegacy => JsonSerializer.SerializeToElement(new
            {
                axiom_closure = frozen.Material.AxiomClosure,
                case_id = frozen.Payload.CaseId,
                input = inputElement,
                input_fingerprint = freshNodeId,
                previous_attestation_event_hash = frozen.LastAttestationEventHash,
                semantic_receipt = freshNodeId,
            }),
            ReattestShape.SchemaV4Legacy => JsonSerializer.SerializeToElement(new
            {
                axiom_closure = frozen.Material.AxiomClosure,
                case_id = frozen.Payload.CaseId,
                input = inputElement,
                previous_attestation_event_hash = frozen.LastAttestationEventHash,
            }),
            ReattestShape.SchemaV4Extended => JsonSerializer.SerializeToElement(new
            {
                axiom_closure = frozen.Material.AxiomClosure,
                case_id = frozen.Payload.CaseId,
                declaration_statement_ids = frozen.Material.DeclarationStatementIds.Select(static item => new
                {
                    declaration_name_key = item.DeclarationNameKey,
                    kind = item.Kind,
                    statement_id = item.StatementId.Value,
                }),
                frozen_node_id = freshNodeId,
                input = inputElement,
                prerequisite_frozen_node_ids = frozen.Material.PrerequisiteFrozenNodeIds.Select(
                    static item => item.Value),
                previous_attestation_event_hash = frozen.LastAttestationEventHash,
                statement_id = frozen.Material.StatementId.Value,
                witness_id = freshNodeId,
            }),
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };
        var reattest = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Reattest",
            reattestPayload,
            shape is ReattestShape.HistoricalLegacy ? 3 : 4);
        files[FrozenLedgerChangeClassifier.AcceptedPath(reattest.Hash)] =
            Encoding.UTF8.GetString(reattest.Bytes.AsSpan());
        var revokedNodeId = shape is ReattestShape.SchemaV4Extended
            ? freshNodeId
            : frozen.Material.FrozenNodeId.Value;
        var revoke = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Revoke",
            JsonSerializer.SerializeToElement(new
            {
                affected_case_ids = Array.Empty<string>(),
                affected_frozen_node_ids = new[] { revokedNodeId },
                closure_hash = FrozenLedgerCanonicalWriter.ZeroHash,
                evidence = Array.Empty<object>(),
                graph_root = FrozenLedgerCanonicalWriter.ZeroHash,
                root_case_ids = Array.Empty<string>(),
                root_frozen_node_ids = new[] { revokedNodeId },
            }));
        files[FrozenLedgerChangeClassifier.AcceptedPath(revoke.Hash)] =
            Encoding.UTF8.GetString(revoke.Bytes.AsSpan());
        return files;
    }

    private enum ReattestShape
    {
        HistoricalLegacy,
        SchemaV4Legacy,
        SchemaV4Extended,
    }

    private static (ImmutableArray<byte> Bytes, string Hash) WriteGenesis(
        int schemaVersion = FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion) =>
        FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Genesis",
            JsonSerializer.SerializeToElement(new
            {
                generator_blob_oid = FrozenLedgerTestData.GitOid('1'),
                origin_commit_oid = FrozenLedgerTestData.GitOid('2'),
                origin_tree_oid = FrozenLedgerTestData.GitOid('3'),
                protocol_version = 1,
                rule_catalog_root = RuleCatalog.Default.RootSha256,
            }),
            schemaVersion);

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
