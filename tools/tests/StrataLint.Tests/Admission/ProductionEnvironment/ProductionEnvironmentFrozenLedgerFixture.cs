using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void CheckAdmitsAValidatedRevokeAndTheCorrespondingClosedModuleRemoval()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = TrustedFrozenFixtureWithLedger(out _);
        var baseView = FrozenLedgerBaseViewReader.Read(Decode(Snapshot(fixture.Baseline)));
        var baselineLedger = baseView.ToWriterBaseline();
        var node = baselineLedger.ActiveFrozenNodes.Single(
            static item => item.RepoPath.Value == RuleFixture.RingPath);
        var provisional = new RevocationEvidence.KernelWitnessFailure(
            node.FrozenNodeId,
            node.WitnessId,
            string.Empty,
            string.Empty);
        var receiptBytes = RevocationReceiptWriter.Write(baselineLedger, provisional);
        var receiptText = Encoding.UTF8.GetString(receiptBytes.AsSpan());
        var receiptOid = FrozenLedgerTestData.GitBlobOid(receiptText);
        var receiptSha = FrozenLedgerTestData.Sha256(receiptText);
        const string receiptPath = "Evidence/D5/S0/Carrier/Ring.run.json";
        fixture.Files[receiptPath] = receiptText;
        fixture.Baseline[receiptPath] = receiptText;
        var receipts = Assert.IsType<RevocationReceiptStoreOutcome.Accepted>(
            TrustedRevocationReceiptStore.Materialize(
                baselineLedger,
                Decode(Snapshot(fixture.Baseline)),
                [receiptOid])).Capability;
        var evidence = provisional with
        {
            ReceiptBlobOid = receiptOid,
            ReceiptSha256 = receiptSha,
        };
        var validated = Assert.IsType<RevocationEvidenceValidationOutcome.Accepted>(
            RevocationEvidenceValidator.Validate(evidence, baselineLedger, receipts)).Capability;
        var plan = Assert.IsType<RevocationPlanOutcome.Accepted>(
            RevocationPlanner.Plan(baselineLedger, [validated])).Capability;
        var revokedBytes = FrozenLedgerGenerator.AppendRevocation(baselineLedger, plan);
        var revokeLine = FrozenLedgerTestData.Lines(revokedBytes)[^1];
        using var revokeDocument = JsonDocument.Parse(
            revokeLine.AsMemory(0, revokeLine.Length - 1));
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Revoke",
            revokeDocument.RootElement.GetProperty("payload"));
        var path = FrozenLedgerChangeClassifier.AcceptedPath(encoded.Hash);
        fixture.Files[path] = Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
        fixture.Files.Remove(RuleFixture.RingPath);
        fixture.Reports.Remove(RuleFixture.RingPath);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.CreateWithKinds(
                [
                    (RuleFixture.RingPath, RawChangeKind.Deleted),
                    (path, RawChangeKind.Added),
                ]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        if (outcome is AdmissionOutcome.RuleRejected rejected)
        {
            Assert.Fail(string.Join("\n", rejected.Diagnostics.Select(static item =>
                $"{item.Path}: {item.Message}")));
        }

        Assert.IsType<AdmissionOutcome.Admitted>(outcome);
    }

    [Fact]
    public void CheckDoesNotValidateLedgerAnchorsWhenNoEventIsAdded()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Baseline["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Files["Meta/domains.yaml"] = TestRegistry.Domains;
        fixture.Baseline["Meta/domains.yaml"] = TestRegistry.Domains;
        AddFrozenLedger(fixture);
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create(new[] { RuleFixture.BlueprintPath }),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline),
            frozenReferenceValidator: static _ => throw new FrozenReferenceRejectionException(
                FrozenReferenceRejectionKind.MissingObject,
                "anchor validation must not run for changesets that add no ledger event"));
        var ledger = new ProductionFrozenLedgerAdmissionServices(
            "/repo",
            ImmutableHashSet<string>.Empty);
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null),
            scribeEmissionVerifier: null,
            ledger);

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        Assert.IsType<AdmissionOutcome.Admitted>(outcome);
        Assert.Equal(0, ledger.BaseViewReadCount);
        Assert.Equal(0, ledger.AdmissionCatalogBuildCount);
        Assert.Equal(0, ledger.IncrementalValidationCount);
        Assert.Equal(0, gateway.FrozenReferenceValidationCount);
    }

    [Fact]
    public void CheckRejectsAddedFreezeWithoutAxiomClosureAndNamesNodePath()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = AddedFrozenRingFixture();
        var freezePath = AddedFreezePathFor(fixture, RuleFixture.RingPath);
        freezePath = RewriteFreezeWithoutAxiomClosure(
            fixture.Files,
            freezePath,
            FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion);
        var addedLedgerPaths = AddedLedgerPaths(fixture);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.CreateWithKinds(
                    addedLedgerPaths.Select(static path => (path, RawChangeKind.Added))),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var diagnostic = Assert.Single(
            rejected.Diagnostics.Where(static item => item.RuleId == RuleId.CreateKnown(8)));
        Assert.Equal(RuleFixture.RingPath, diagnostic.Path);
        Assert.Contains(
            $"Added Freeze event for {RuleFixture.RingPath} must carry axiom_closure.",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains("delta witness: " + freezePath, diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CheckAdmitsHistoricalClosurelessV2FreezeDuringIncrementalEvaluation()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = TrustedFrozenFixture();
        var freezePath = FreezePathFor(fixture, RuleFixture.RingPath);
        var historicalPath = RewriteFreezeWithoutAxiomClosure(
            fixture.Files,
            freezePath,
            schemaVersion: 2);
        Assert.Equal(
            historicalPath,
            RewriteFreezeWithoutAxiomClosure(fixture.Baseline, freezePath, schemaVersion: 2));
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.CreateWithKinds([(RuleFixture.RingPath, RawChangeKind.Modified)]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        Assert.IsType<AdmissionOutcome.Admitted>(outcome);
    }

    [Fact]
    public void CheckAdmitsAddedFreezeAnchoredToPhaseAWhenCurrentRevisionIsPhaseB()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Baseline["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Files["Meta/domains.yaml"] = TestRegistry.Domains;
        fixture.Baseline["Meta/domains.yaml"] = TestRegistry.Domains;
        AddFrozenLedger(fixture);
        var addedLedgerPaths = AddedLedgerPaths(fixture);
        Assert.NotEmpty(addedLedgerPaths);
        Assert.All(addedLedgerPaths, path =>
        {
            using var document = JsonDocument.Parse(fixture.Files[path]);
            Assert.Equal("Freeze", document.RootElement.GetProperty("event_type").GetString());
            var input = document.RootElement.GetProperty("payload").GetProperty("input");
            Assert.Equal(
                FrozenLedgerTestData.GitOid('a'),
                input.GetProperty("base_commit_oid").GetString());
            Assert.Equal(
                FrozenLedgerTestData.GitOid('b'),
                input.GetProperty("base_tree_oid").GetString());
        });
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.CreateWithKinds(
                addedLedgerPaths.Select(static path => (path, RawChangeKind.Added))),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline),
            currentRevisionResolver: static () => new FrozenRevisionIdentity(
                new string('c', 40),
                FrozenLedgerTestData.GitOid('c'),
                FrozenLedgerTestData.GitOid('d')));
        var ledger = new ProductionFrozenLedgerAdmissionServices(
            "/repo",
            ImmutableHashSet<string>.Empty);
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null),
            scribeEmissionVerifier: null,
            ledger);

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        Assert.True(
            outcome is AdmissionOutcome.Admitted,
            outcome switch
            {
                AdmissionOutcome.RuleRejected rejected => string.Join(
                    '\n',
                    rejected.Diagnostics.Select(static diagnostic => diagnostic.Render())),
                AdmissionOutcome.InfrastructureFailure failure => failure.Message,
                _ => outcome.ToString(),
            });
        Assert.Equal(1, ledger.BaseViewReadCount);
        Assert.Equal(1, ledger.DeltaEventLoadCount);
        Assert.Equal(1, ledger.AdmissionCatalogBuildCount);
        Assert.Equal(1, ledger.IncrementalValidationCount);
        Assert.Equal(1, gateway.CurrentRevisionResolutionCount);
        var deltaReferences = Assert.Single(gateway.FrozenReferenceValidations);
        Assert.Contains(FrozenLedgerTestData.GitOid('a'), deltaReferences.CommitOids);
        Assert.Equal(
            FrozenLedgerTestData.GitOid('a'),
            Assert.Single(deltaReferences.RequiredAncestorCommitOids));
    }

    [Fact]
    public void CheckRetainsScopedMaterialBlobDriftDetection()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = TrustedFrozenFixture();
        fixture.Files[RuleFixture.RingPath] += "\n-- material drift\n";
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.CreateWithKinds([(RuleFixture.RingPath, RawChangeKind.Modified)]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var diagnostic = Assert.Single(
            rejected.Diagnostics.Where(static item => item.RuleId == RuleId.CreateKnown(8)));
        Assert.Equal(RuleFixture.RingPath, diagnostic.Path);
        Assert.Contains("material/blob drift", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains(
            "delta witness: " + RuleFixture.RingPath,
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    private static RuleFixture TrustedFrozenFixtureWithLedger(
        out FrozenLedgerConsistent baselineLedger)
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        baselineLedger = AddFrozenLedger(fixture);
        foreach (var item in fixture.Files)
        {
            fixture.Baseline[item.Key] = item.Value;
        }
        foreach (var item in fixture.Reports)
        {
            fixture.BaselineReports[item.Key] = item.Value;
        }

        return fixture;
    }

    private static string AddIncompleteReattest(RuleFixture fixture)
    {
        var payload = JsonSerializer.SerializeToElement(new
        {
            frozen_node_id = "sha256:" + new string('9', 64),
            input = new
            {
                base_commit_oid = FrozenLedgerTestData.GitOid('a'),
                base_tree_oid = FrozenLedgerTestData.GitOid('b'),
                descriptor_blob_oid = FrozenLedgerTestData.GitBlobOid(
                    fixture.Files[RuleFixture.RingPath]),
                descriptor_selector = RuleFixture.RingPath,
                materializer = "repository-snapshot-v1",
                supporting_blob_oids = Array.Empty<string>(),
            },
        });
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent("Reattest", payload);
        var identity = FrozenLedgerCanonicalWriter.EventIdentity(
            "Reattest",
            payload,
            encoded.Hash);
        var path = FrozenLedgerChangeClassifier.AcceptedPath(identity);
        fixture.Files[path] = Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
        return path;
    }

    private static string AddMatchingReattest(
        RuleFixture fixture,
        FrozenLedgerConsistent baselineLedger,
        out ImmutableArray<byte> reattestedLedger)
    {
        var candidateCatalog = BuildFrozenCatalog(fixture.Files, fixture.Reports);
        reattestedLedger = FrozenLedgerGenerator.AppendReattestation(
            baselineLedger,
            candidateCatalog);
        SetLedger(fixture.Files, Encoding.UTF8.GetString(reattestedLedger.AsSpan()));
        return Assert.Single(AddedLedgerPaths(fixture), path => EventType(fixture.Files[path]) == "Reattest");
    }

    private static FrozenMaterialCatalog BuildFrozenCatalog(
        IReadOnlyDictionary<string, string> files,
        IReadOnlyDictionary<string, LeanFileReport> reports)
    {
        var (snapshot, lean, dag) = BuildState(files, reports);
        var attestations = dag.Nodes
            .Where(static node => node.State is TruthState.Closed && node.ModuleName is not null)
            .Select(node => new FrozenModuleAttestation(
                node.RepoPath,
                FrozenLedgerTestData.GitBlobOid(files[node.RepoPath.Value]))
            {
                BaseCommitOid = FrozenLedgerTestData.GitOid('a'),
                BaseTreeOid = FrozenLedgerTestData.GitOid('b'),
            });
        return Assert.IsType<FrozenMaterialOutcome.Accepted>(
            FrozenContentAddress.Build(snapshot, lean, dag, FrozenEnvironment(files), attestations)).Capability;
    }

    private static FrozenEnvironmentAttestation FrozenEnvironment(
        IReadOnlyDictionary<string, string> files) => new(
            FrozenLedgerTestData.GitOid('a'),
            FrozenLedgerTestData.GitOid('b'),
            FrozenLedgerTestData.GitBlobOid(files["lean-toolchain"]),
            FrozenLedgerTestData.GitBlobOid(files["lake-manifest.json"]))
        {
            LakefilePath = "lakefile.toml",
            LakefileBlobOid = FrozenLedgerTestData.GitBlobOid(files["lakefile.toml"]),
        };

    private static FrozenEnvironmentPins FrozenPins(FrozenEnvironmentAttestation environment) => new(
        environment.LakeManifestBlobOid,
        environment.LakefileBlobOid!,
        RepoPath.CreateKnown(environment.LakefilePath!),
        environment.LeanToolchainBlobOid);

    private static ImmutableArray<string> EnvironmentOids(FrozenEnvironmentPins environment) =>
        new[]
        {
            environment.LakeManifestBlobOid,
            environment.LakefileBlobOid,
            environment.LeanToolchainBlobOid,
        }.Order(StringComparer.Ordinal).ToImmutableArray();

    private static string EventType(string contents)
    {
        using var document = JsonDocument.Parse(contents);
        return document.RootElement.GetProperty("event_type").GetString()!;
    }

    private static string RewriteFreezeWithoutAxiomClosure(
        IDictionary<string, string> files,
        string eventPath,
        int schemaVersion)
    {
        using var document = JsonDocument.Parse(files[eventPath]);
        var root = document.RootElement;
        Assert.Equal("Freeze", root.GetProperty("event_type").GetString());
        var payload = JsonNode.Parse(root.GetProperty("payload").GetRawText())!.AsObject();
        Assert.True(payload.Remove("axiom_closure"));
        if (schemaVersion == 2)
        {
            var input = payload["input"]!.AsObject();
            payload["case_class"] = "active-frozen";
            payload["evaluation"] = "admission";
            payload["expected"] = new JsonObject
            {
                ["allowed_dispositions"] = new JsonArray("admit"),
                ["diagnostic_match"] = "none",
                ["required_diagnostics"] = new JsonArray(),
            };
            payload["input_fingerprint"] = payload["witness_id"]!.GetValue<string>();
            payload["node_path"] = input["descriptor_selector"]!.GetValue<string>();
            payload["semantic_receipt"] = payload["frozen_node_id"]!.GetValue<string>();
            payload["truth_state"] = nameof(TruthState.Closed);
        }

        var payloadElement = JsonSerializer.SerializeToElement(payload);
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Freeze",
            payloadElement,
            schemaVersion);
        var identity = FrozenLedgerCanonicalWriter.EventIdentity(
            "Freeze",
            payloadElement,
            encoded.Hash,
            schemaVersion);
        var rewrittenPath = FrozenLedgerChangeClassifier.AcceptedPath(identity);
        files.Remove(eventPath);
        files[rewrittenPath] = Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
        return rewrittenPath;
    }
}
