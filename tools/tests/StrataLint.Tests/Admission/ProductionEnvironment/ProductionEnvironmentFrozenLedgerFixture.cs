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
        var revokeFile = Assert.Single(DagLedgerAppendWriter.BuildNewEventFiles(
            FrozenLedgerGenerator.Revocation(baselineLedger, plan)));
        var path = revokeFile.Path.Value;
        fixture.Files[path] = revokeFile.Text;
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
    public void CheckAllowsScopedMaterialBlobDriftWhenFrozenIdentityIsStable()
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

        Assert.IsType<AdmissionOutcome.Admitted>(outcome);
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
        var payloadElement = JsonSerializer.SerializeToElement(payload);
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Freeze",
            payloadElement,
            schemaVersion);
        var identity = FrozenLedgerCanonicalWriter.EventIdentity(encoded.Hash);
        var rewrittenPath = FrozenLedgerChangeClassifier.AcceptedPath(identity);
        files.Remove(eventPath);
        files[rewrittenPath] = Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
        return rewrittenPath;
    }
}
