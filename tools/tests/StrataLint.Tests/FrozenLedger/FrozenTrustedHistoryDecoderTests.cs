using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class FrozenTrustedHistoryDecoderTests
{
    private const string TargetCase = "historical-target";
    private const string DependencyCase = "historical-dependency";
    private const string TargetPath = "D5/S0/Carrier/A.lean";
    private const string DependencyPath = "D5/S0/Carrier/B.lean";

    [Fact]
    public void TrustedHistoryDecoderConsumesReattestV2ExtendedPayload()
    {
        var view = ReadView(
            Genesis(),
            FreezeV2('1', TargetCase, TargetPath, 'a', 'b', []),
            ReattestV2Extended('2', '1', TargetCase, TargetPath, 'c', 'd', []));

        var active = Assert.Single(view.ActiveByCase).Value;
        Assert.Equal(Hash('c'), active.Material.StatementId.Value);
        Assert.Equal(Hash('d'), active.Material.FrozenNodeId.Value);
        Assert.Equal(new[] { "second", "first" },
            active.Material.DeclarationStatementIds.Select(static item => item.DeclarationNameKey));
    }

    [Fact]
    public void TrustedHistoryDecoderConsumesReattestV3ClosurePayload()
    {
        var view = ReadView(
            Genesis(),
            FreezeV2('1', TargetCase, TargetPath, 'a', 'b', []),
            ReattestV3Closure('2', '1', TargetCase, TargetPath, Hash('b')));

        var active = Assert.Single(view.ActiveByCase).Value;
        Assert.Equal(Hash('a'), active.Material.StatementId.Value);
        Assert.Equal(Hash('b'), active.Material.FrozenNodeId.Value);
        Assert.Equal(new[] { "Classical.choice", "propext" }, active.Material.AxiomClosure);
    }

    [Fact]
    public void TrustedHistoryDecoderConsumesReattestV4ExtendedPayload()
    {
        var view = ReadView(
            Genesis(),
            FreezeV2('1', TargetCase, TargetPath, 'a', 'b', []),
            ReattestV4Extended('2', '1', TargetCase, TargetPath, 'c', 'd', []));

        var active = Assert.Single(view.ActiveByCase).Value;
        Assert.Equal(Hash('c'), active.Material.StatementId.Value);
        Assert.Equal(Hash('d'), active.Material.FrozenNodeId.Value);
        Assert.Equal(new[] { "Classical.choice", "Quot.sound" }, active.Material.AxiomClosure);
    }

    [Fact]
    public void TrustedHistoryProjectionFoldsFreezeV2ExtendedV3ClosureChain()
    {
        var dependencyFrozenId = Hash('7');
        var view = ReadView(
            Genesis(),
            FreezeV2('0', DependencyCase, DependencyPath, '6', '7', []),
            FreezeV2('1', TargetCase, TargetPath, 'a', 'b', []),
            ReattestV2Extended(
                '2', '1', TargetCase, TargetPath, 'c', 'd', [dependencyFrozenId]),
            ReattestV3Closure('3', '2', TargetCase, TargetPath, Hash('d')));

        var target = view.ActiveByPath[RepoPath.CreateKnown(TargetPath)];
        var pathsByIdentity = view.ActiveByPath.Values.ToDictionary(
            static item => item.Material.FrozenNodeId,
            static item => item.Material.RepoPath);
        var prerequisitePaths = target.Material.PrerequisiteFrozenNodeIds
            .Select(identity => pathsByIdentity[identity].Value)
            .ToArray();

        Assert.Equal(Hash('c'), target.Material.StatementId.Value);
        Assert.Equal(new[] { "second", "first" },
            target.Material.DeclarationStatementIds.Select(static item => item.DeclarationNameKey));
        Assert.Equal(TargetPath, target.Material.RepoPath.Value);
        Assert.Equal(TargetPath, target.Payload.Input.DescriptorSelector);
        Assert.Equal(Hash('d'), target.Material.FrozenNodeId.Value);
        Assert.Equal(new[] { DependencyPath }, prerequisitePaths);
        Assert.Equal(new[] { "Classical.choice", "propext" }, target.Material.AxiomClosure);
    }

    [Fact]
    public void TrustedHistoryProjectionRejectsAttestationCycle()
    {
        var exception = Assert.Throws<InvalidOperationException>(() => ReadView(
            Genesis(),
            FreezeV2('1', TargetCase, TargetPath, 'a', 'b', []),
            ReattestV3Closure('2', '3', TargetCase, TargetPath, Hash('b')),
            ReattestV3Closure('3', '2', TargetCase, TargetPath, Hash('b'))));

        Assert.Contains("cycle", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void TrustedHistoryProjectionRejectsMissingAttestationParent()
    {
        var exception = Assert.Throws<InvalidOperationException>(() => ReadView(
            Genesis(),
            FreezeV2('1', TargetCase, TargetPath, 'a', 'b', []),
            ReattestV3Closure('2', '9', TargetCase, TargetPath, Hash('b'))));

        Assert.Contains("absent predecessor", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void TrustedHistoryReaderDoesNotRestoreCandidateReattestWriterOrCliVerb()
    {
        var view = ReadView(
            Genesis(),
            FreezeV2('1', TargetCase, TargetPath, 'a', 'b', []),
            ReattestV4Extended('2', '1', TargetCase, TargetPath, 'c', 'd', []));
        Assert.Single(view.ActiveByCase);

        var candidatePayload = ReattestV4Payload(
            TargetCase,
            TargetPath,
            Hash('c'),
            Hash('d'),
            [],
            Hash('2'),
            includeHistoricalMaterializer: false);
        var candidate = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Reattest",
            JsonSerializer.SerializeToElement(candidatePayload));
        var candidatePath = FrozenLedgerChangeClassifier.AcceptedPath(candidate.Hash);
        var candidateSnapshot = Snapshot(new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [candidatePath] = Encoding.UTF8.GetString(candidate.Bytes.AsSpan()),
        });
        var invalid = Assert.IsType<DagLedgerFilesLoadOutcome.Invalid>(
            FrozenAcceptedEventLoader.LoadFiles(candidateSnapshot.Files.Values));
        Assert.Contains("Unknown frozen event type Reattest", invalid.Message, StringComparison.Ordinal);

        var console = new BufferedConsole();
        var exitCode = CliApplication.Run(
            ["ledger-reattest"],
            new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused")),
            console);
        Assert.Equal(2, exitCode);
        Assert.Equal("UNKNOWN_COMMAND ledger-reattest\n", console.Error);
        Assert.DoesNotContain("ledger-reattest", CliApplication.ImplementedCommands);
    }

    [Fact]
    public void TrustedReferenceScanAcceptsFreezeV2AndV3PayloadShapes()
    {
        foreach (var historical in new[]
        {
            FreezeV2('1', TargetCase, TargetPath, 'a', 'b', []),
            FreezeV3('2', TargetCase, TargetPath, 'a', 'b', []),
        })
        {
            var accepted = Assert.IsType<FrozenLedgerReferenceScanOutcome.Accepted>(
                ScanTrustedReferences(historical));

            Assert.Equal(TargetPath, Assert.Single(accepted.References.Inputs).DescriptorSelector);
        }
    }

    [Fact]
    public void TrustedReferenceScanAcceptsHistoricalInputMaterializer()
    {
        var accepted = Assert.IsType<FrozenLedgerReferenceScanOutcome.Accepted>(
            ScanTrustedReferences(
                FreezeV4('1', TargetCase, TargetPath, 'a', 'b', historicalInput: true)));

        Assert.Equal(TargetPath, Assert.Single(accepted.References.Inputs).DescriptorSelector);
    }

    [Fact]
    public void TrustedReferenceScanConsumesLegacyFreezeProjectionFields()
    {
        var historical = FreezeV2('1', TargetCase, TargetPath, 'a', 'b', []);
        Assert.IsType<FrozenLedgerReferenceScanOutcome.Accepted>(
            ScanTrustedReferences(historical));
        var mutations = new (string Field, Action<JsonObject> Apply)[]
        {
            ("case_class", payload => { payload["case_class"] = 7; }),
            ("evaluation", payload => { payload["evaluation"] = 7; }),
            ("allowed_dispositions", payload =>
            {
                payload["expected"]!.AsObject()["allowed_dispositions"] = "admit";
            }),
            ("diagnostic_match", payload =>
            {
                payload["expected"]!.AsObject()["diagnostic_match"] = new JsonArray();
            }),
            ("required_diagnostics", payload =>
            {
                payload["expected"]!.AsObject()["required_diagnostics"] = "none";
            }),
            ("input_fingerprint", payload => { payload["input_fingerprint"] = 7; }),
            ("node_path", payload => { payload["node_path"] = 7; }),
            ("semantic_receipt", payload => { payload["semantic_receipt"] = 7; }),
            ("truth_state", payload => { payload["truth_state"] = 7; }),
        };

        foreach (var (field, mutate) in mutations)
        {
            var invalid = Assert.IsType<DagLedgerFilesLoadOutcome.Invalid>(
                LoadTrusted(MutatePayload(historical, mutate)));
            Assert.Contains(field, invalid.Message, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void TrustedReferenceScanConsumesLegacyReattestPayloadFields()
    {
        foreach (var historical in new[]
        {
            ReattestV2Extended('2', '1', TargetCase, TargetPath, 'c', 'd', []),
            ReattestV3Closure('3', '2', TargetCase, TargetPath, Hash('d')),
        })
        {
            var accepted = Assert.IsType<FrozenLedgerReferenceScanOutcome.Accepted>(
                ScanTrustedReferences(historical));
            Assert.Equal(TargetPath, Assert.Single(accepted.References.Inputs).DescriptorSelector);

            var invalid = Assert.IsType<DagLedgerFilesLoadOutcome.Invalid>(LoadTrusted(
                MutatePayload(historical, payload =>
                {
                    payload["previous_attestation_event_hash"] = 7;
                })));
            Assert.Contains("previous_attestation_event_hash", invalid.Message, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void CandidateLoaderStillRejectsLegacyAcceptedEventShapes()
    {
        var historicalSchema = Assert.IsType<DagLedgerFilesLoadOutcome.Invalid>(
            LoadCandidate(FreezeV2('1', TargetCase, TargetPath, 'a', 'b', [])));
        Assert.Contains("schema_version must be 4", historicalSchema.Message, StringComparison.Ordinal);

        var historicalInput = Assert.IsType<DagLedgerFilesLoadOutcome.Invalid>(LoadCandidate(
            CanonicalDagEvent(
                FreezeV4('2', TargetCase, TargetPath, 'a', 'b', historicalInput: true))));
        Assert.Contains("unknown, missing, or duplicate fields", historicalInput.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void EveryAcceptedHeadEventHasATrustedHistoryDecoder()
    {
        var root = TestRepositoryLayout.FindRoot();
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(new GitRepositoryGateway(root).ReadCurrent())).Snapshot;
        var acceptedCount = snapshot.Files.Count(static item =>
            FrozenLedgerChangeClassifier.IsAcceptedEventPath(item.Key.Value));

        var view = FrozenLedgerBaseViewReader.Read(snapshot);
        var eventsByHash = view.Events.ToDictionary(
            static item => item.EventHash,
            StringComparer.Ordinal);
        var activeIdentities = view.ActiveByCase.Values
            .Select(static entry => entry.Material.FrozenNodeId)
            .ToHashSet();
        var prerequisiteEdges = view.ActiveByCase.Values
            .SelectMany(static entry => entry.Material.PrerequisiteFrozenNodeIds)
            .ToArray();
        var unresolvedEdges = prerequisiteEdges
            .Where(identity => !activeIdentities.Contains(identity))
            .ToArray();
        var unresolvedModules = view.ActiveByCase.Values.Count(entry =>
            entry.Material.PrerequisiteFrozenNodeIds.Any(identity =>
                !activeIdentities.Contains(identity)));

        Assert.Equal(acceptedCount, view.EventCount);
        Assert.NotEmpty(view.Events);
        Assert.All(view.ActiveByCase.Values, entry =>
            Assert.True(eventsByHash.ContainsKey(entry.LastAttestationEventHash)));
        Assert.Empty(unresolvedEdges.Select(static identity => identity.Value).Distinct());
        Assert.Empty(unresolvedEdges);
        Assert.Equal(0, unresolvedModules);
    }

    private static FrozenLedgerBaseView ReadView(params EventFixture[] events) =>
        FrozenLedgerBaseViewReader.Read(Snapshot(events.ToDictionary(
            static item => FrozenLedgerChangeClassifier.AcceptedPath(Hash(item.HashDigit)),
            static item => item.Json,
            StringComparer.Ordinal)));

    private static FrozenLedgerReferenceScanOutcome ScanTrustedReferences(EventFixture item)
    {
        var loaded = Assert.IsType<DagLedgerFilesLoadOutcome.Loaded>(LoadTrusted(item));
        return FrozenLedger.ScanReferences(loaded.Events);
    }

    private static DagLedgerFilesLoadOutcome LoadTrusted(EventFixture item) =>
        FrozenAcceptedEventLoader.LoadTrustedFiles(EventFiles(item));

    private static DagLedgerFilesLoadOutcome LoadCandidate(EventFixture item) =>
        FrozenAcceptedEventLoader.LoadFiles(EventFiles(item));

    private static IEnumerable<RepositoryFile> EventFiles(EventFixture item)
    {
        using var document = JsonDocument.Parse(item.Json);
        var eventHash = document.RootElement.GetProperty("event_hash").GetString()!;
        return Snapshot(new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [FrozenLedgerChangeClassifier.AcceptedPath(eventHash)] = item.Json,
        }).Files.Values;
    }

    private static RepositorySnapshot Snapshot(IReadOnlyDictionary<string, string> files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(files.Select(static pair =>
                RawRepositoryEntry.FromText(pair.Key, pair.Value))))).Snapshot;

    private static EventFixture Genesis() => Event(
        'f',
        "Genesis",
        2,
        new Dictionary<string, object?>(StringComparer.Ordinal)
        {
            ["generator_blob_oid"] = GitOid('1'),
            ["origin_commit_oid"] = GitOid('2'),
            ["origin_tree_oid"] = GitOid('3'),
            ["protocol_version"] = 1,
            ["rule_catalog_root"] = Hash('4'),
        });

    private static EventFixture FreezeV2(
        char eventHash,
        string caseId,
        string path,
        char statement,
        char frozen,
        string[] prerequisites) => Event(
            eventHash,
            "Freeze",
            2,
            new Dictionary<string, object?>(StringComparer.Ordinal)
            {
                ["case_class"] = "active-frozen",
                ["case_id"] = caseId,
                ["declaration_statement_ids"] = Declarations(statement),
                ["evaluation"] = "admission",
                ["expected"] = new
                {
                    allowed_dispositions = new[] { "admit" },
                    diagnostic_match = "none",
                    required_diagnostics = Array.Empty<object>(),
                },
                ["frozen_node_id"] = Hash(frozen),
                ["input"] = HistoricalInput(path, eventHash),
                ["input_fingerprint"] = Hash(frozen),
                ["node_path"] = path,
                ["prerequisite_frozen_node_ids"] = prerequisites,
                ["semantic_receipt"] = Hash(frozen),
                ["statement_id"] = Hash(statement),
                ["truth_state"] = "Closed",
                ["witness_id"] = Hash(frozen),
            });

    private static EventFixture FreezeV3(
        char eventHash,
        string caseId,
        string path,
        char statement,
        char frozen,
        string[] prerequisites)
    {
        var v2 = FreezeV2(eventHash, caseId, path, statement, frozen, prerequisites);
        var root = JsonNode.Parse(v2.Json)!.AsObject();
        root["schema_version"] = 3;
        root["payload"]!.AsObject()["axiom_closure"] = new JsonArray("Classical.choice", "propext");
        return new EventFixture(eventHash, root.ToJsonString() + "\n");
    }

    private static EventFixture FreezeV4(
        char eventHash,
        string caseId,
        string path,
        char statement,
        char frozen,
        bool historicalInput) => Event(
            eventHash,
            "Freeze",
            4,
            new Dictionary<string, object?>(StringComparer.Ordinal)
            {
                ["axiom_closure"] = new[] { "Classical.choice", "propext" },
                ["case_id"] = caseId,
                ["declaration_statement_ids"] = Declarations(statement),
                ["frozen_node_id"] = Hash(frozen),
                ["input"] = historicalInput
                    ? HistoricalInput(path, eventHash)
                    : CurrentInput(path, eventHash),
                ["prerequisite_frozen_node_ids"] = Array.Empty<string>(),
                ["statement_id"] = Hash(statement),
                ["witness_id"] = Hash(frozen),
            });

    private static EventFixture ReattestV2Extended(
        char eventHash,
        char previousHash,
        string caseId,
        string path,
        char statement,
        char frozen,
        string[] prerequisites) => Event(
            eventHash,
            "Reattest",
            2,
            new Dictionary<string, object?>(StringComparer.Ordinal)
            {
                ["case_id"] = caseId,
                ["declaration_statement_ids"] = Declarations(statement),
                ["frozen_node_id"] = Hash(frozen),
                ["input"] = HistoricalInput(path, eventHash),
                ["input_fingerprint"] = Hash(frozen),
                ["prerequisite_frozen_node_ids"] = prerequisites,
                ["previous_attestation_event_hash"] = Hash(previousHash),
                ["semantic_receipt"] = Hash(frozen),
                ["statement_id"] = Hash(statement),
                ["witness_id"] = Hash(frozen),
            });

    private static EventFixture ReattestV3Closure(
        char eventHash,
        char previousHash,
        string caseId,
        string path,
        string frozenId) => Event(
            eventHash,
            "Reattest",
            3,
            new Dictionary<string, object?>(StringComparer.Ordinal)
            {
                ["axiom_closure"] = new[] { "Classical.choice", "propext" },
                ["case_id"] = caseId,
                ["input"] = HistoricalInput(path, eventHash),
                ["input_fingerprint"] = Hash(eventHash),
                ["previous_attestation_event_hash"] = Hash(previousHash),
                ["semantic_receipt"] = frozenId,
            });

    private static EventFixture ReattestV4Extended(
        char eventHash,
        char previousHash,
        string caseId,
        string path,
        char statement,
        char frozen,
        string[] prerequisites) => Event(
            eventHash,
            "Reattest",
            4,
            ReattestV4Payload(
                caseId,
                path,
                Hash(statement),
                Hash(frozen),
                prerequisites,
                Hash(previousHash),
                includeHistoricalMaterializer: true));

    private static Dictionary<string, object?> ReattestV4Payload(
        string caseId,
        string path,
        string statementId,
        string frozenId,
        string[] prerequisites,
        string previousHash,
        bool includeHistoricalMaterializer) => new(StringComparer.Ordinal)
        {
            ["axiom_closure"] = new[] { "Classical.choice", "Quot.sound" },
            ["case_id"] = caseId,
            ["declaration_statement_ids"] = Declarations(statementId[^1]),
            ["frozen_node_id"] = frozenId,
            ["input"] = includeHistoricalMaterializer
                ? HistoricalInput(path, statementId[^1])
                : CurrentInput(path, statementId[^1]),
            ["prerequisite_frozen_node_ids"] = prerequisites,
            ["previous_attestation_event_hash"] = previousHash,
            ["statement_id"] = statementId,
            ["witness_id"] = frozenId,
        };

    private static object[] Declarations(char statement) =>
    [
        new
        {
            declaration_name_key = "second",
            kind = "theorem",
            statement_id = Hash(statement),
        },
        new
        {
            declaration_name_key = "first",
            kind = "def",
            statement_id = Hash((char)(statement + 1)),
        },
    ];

    private static object HistoricalInput(string path, char digit) => new
    {
        base_commit_oid = GitOid(digit),
        base_tree_oid = GitOid(digit),
        descriptor_blob_oid = GitOid(digit),
        descriptor_selector = path,
        materializer = "repository-snapshot-v1",
        supporting_blob_oids = new[] { GitOid('8'), GitOid('9') },
    };

    private static object CurrentInput(string path, char digit) => new
    {
        base_commit_oid = GitOid(digit),
        base_tree_oid = GitOid(digit),
        descriptor_blob_oid = GitOid(digit),
        descriptor_selector = path,
        supporting_blob_oids = new[] { GitOid('8'), GitOid('9') },
    };

    private static EventFixture Event(
        char hashDigit,
        string eventType,
        int schemaVersion,
        object payload) => new(
            hashDigit,
            JsonSerializer.Serialize(new
            {
                event_hash = Hash(hashDigit),
                event_type = eventType,
                payload,
                schema_version = schemaVersion,
            }) + "\n");

    private static EventFixture MutatePayload(
        EventFixture item,
        Action<JsonObject> mutation)
    {
        var root = JsonNode.Parse(item.Json)!.AsObject();
        mutation(root["payload"]!.AsObject());
        return item with { Json = root.ToJsonString() + "\n" };
    }

    private static EventFixture CanonicalDagEvent(EventFixture item)
    {
        using var document = JsonDocument.Parse(item.Json);
        var root = document.RootElement;
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
            root.GetProperty("event_type").GetString()!,
            root.GetProperty("payload"),
            root.GetProperty("schema_version").GetInt32());
        return item with { Json = Encoding.UTF8.GetString(encoded.Bytes.AsSpan()) };
    }

    private static string Hash(char digit) => $"sha256:{new string(digit, 64)}";

    private sealed record EventFixture(char HashDigit, string Json);
}
