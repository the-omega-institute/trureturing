using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void CheckRejectsAnAddedRevokeWithItsDeltaPathAsWitness()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Baseline["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Files["Meta/domains.yaml"] = TestRegistry.Domains;
        fixture.Baseline["Meta/domains.yaml"] = TestRegistry.Domains;
        AddFrozenLedger(fixture);
        var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
            "Revoke",
            JsonSerializer.SerializeToElement(new
            {
                affected_case_ids = Array.Empty<string>(),
                affected_frozen_node_ids = Array.Empty<string>(),
                closure_hash = "sha256:" + new string('1', 64),
                evidence = Array.Empty<object>(),
                graph_root = "sha256:" + new string('2', 64),
                root_case_ids = Array.Empty<string>(),
                root_frozen_node_ids = Array.Empty<string>(),
            }));
        var path = FrozenLedgerChangeClassifier.AcceptedPath(encoded.Hash);
        fixture.Files[path] = Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.CreateWithKinds([(path, RawChangeKind.Added)]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var diagnostic = Assert.Single(
            rejected.Diagnostics.Where(static item => item.RuleId == RuleId.CreateKnown(8)));
        Assert.Equal(path, diagnostic.Path);
        Assert.Contains(
            "incremental admission does not support Revoke",
            diagnostic.Message,
            StringComparison.Ordinal);
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
    public void CheckValidatesBothEnvironmentReferencesOfAnAddedRecoordinateEvent()
    {
        var (path, contents) = FrozenLedgerTests.EnvironmentRecoordinateDagEvent();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        AddFrozenLedger(fixture);
        fixture.Files[path] = contents;
        FrozenLedgerReferenceSet? captured = null;
        var service = new ProductionFrozenLedgerAdmissionServices(
            "/repo",
            ImmutableHashSet<string>.Empty);

        var failure = Assert.Throws<FrozenLedgerAdmissionPreparationException>(() =>
            service.Prepare(
                Decode(Snapshot(fixture.Files)),
                Decode(Snapshot(fixture.Baseline)),
                RawChangeSet.CreateWithKinds([(path, RawChangeKind.Added)]),
                references =>
                {
                    captured = references;
                    throw new FrozenReferenceRejectionException(
                        FrozenReferenceRejectionKind.MissingObject,
                        "synthetic added EnvironmentRecoordinate anchor rejection");
                }));

        Assert.Contains(
            "synthetic added EnvironmentRecoordinate anchor rejection",
            failure.Message,
            StringComparison.Ordinal);
        Assert.Equal(path, Assert.Single(failure.Paths).Value);
        Assert.NotNull(captured);
        Assert.Equal(2, captured.Inputs.Length);
        Assert.Equal(2, captured.EnvironmentReferences.Length);
        Assert.Empty(captured.RequiredAncestorCommitOids);
        var oldReference = Assert.Single(
            captured.EnvironmentReferences,
            reference => reference.Input.BaseCommitOid == FrozenLedgerTestData.GitOid('a'));
        var newReference = Assert.Single(
            captured.EnvironmentReferences,
            reference => reference.Input.BaseCommitOid == FrozenLedgerTestData.GitOid('c'));
        Assert.Equal(FrozenLedgerTestData.GitOid('b'), oldReference.Input.BaseTreeOid);
        Assert.Equal(FrozenLedgerTestData.GitOid('d'), newReference.Input.BaseTreeOid);
        Assert.NotEqual(
            oldReference.Environment.LeanToolchainBlobOid,
            newReference.Environment.LeanToolchainBlobOid);
        Assert.NotEqual(
            oldReference.Environment.LakeManifestBlobOid,
            newReference.Environment.LakeManifestBlobOid);
        Assert.Equal("lakefile.toml", oldReference.Environment.LakefilePath.Value);
        Assert.Equal("lakefile.toml", newReference.Environment.LakefilePath.Value);
        Assert.Equal(FrozenLedgerTestData.PathFor("A"), oldReference.Input.DescriptorSelector);
        Assert.Equal(FrozenLedgerTestData.PathFor("A"), newReference.Input.DescriptorSelector);
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

    private static void DriftEnvironmentAndStatementIdentity(RuleFixture fixture, string statementType)
    {
        fixture.Files["lean-toolchain"] = "leanprover/lean4:v4.25.0\n";
        fixture.Reports[RuleFixture.RingPath] = new LeanFileReport(
            [],
            [new LeanDeclaration("goldenRing", "def", statementType, [])]);
    }

    private static string AddEnvironmentRecoordinate(
        RuleFixture fixture,
        FrozenLedgerConsistent baselineLedger,
        LeanFileReport eventReport)
    {
        _ = baselineLedger;
        var eventReports = new Dictionary<string, LeanFileReport>(fixture.Reports, StringComparer.Ordinal)
        {
            [RuleFixture.RingPath] = eventReport,
        };
        var candidateCatalog = BuildFrozenCatalog(fixture.Files, eventReports);
        var baseView = FrozenLedgerBaseViewReader.Read(Decode(Snapshot(fixture.Baseline)));
        var oldEnvironment = FrozenEnvironment(fixture.Baseline);
        var newEnvironment = FrozenEnvironment(fixture.Files);
        var oldPins = FrozenPins(oldEnvironment);
        var newPins = FrozenPins(newEnvironment);
        string? ringEventPath = null;
        foreach (var active in baseView.ActiveByPath.Values.OrderBy(
            static entry => entry.Material.RepoPath.Value,
            StringComparer.Ordinal))
        {
            var modulePath = active.Material.RepoPath;
            var candidate = candidateCatalog.ByPath[modulePath];
            var newReport = eventReports[modulePath.Value];
            var oldReport = fixture.BaselineReports[modulePath.Value];
            var oldInput = active.Payload.Input with
            {
                SupportingBlobOids = EnvironmentOids(oldPins),
            };
            var newInput = FrozenLedgerCanonicalWriter.FreezePayload(newEnvironment, candidate).Input with
            {
                SupportingBlobOids = EnvironmentOids(newPins),
            };
            var payload = new FrozenEnvironmentRecoordinatePayload(
                active.Payload.CaseId,
                candidate.DeclarationStatementIds,
                active.Material.DeclarationStatementIds,
                newPins,
                oldPins,
                FrozenLedger.EnvironmentRecoordinateUnprovedEquivalence,
                nameof(TruthState.Closed),
                candidate.AxiomClosure,
                candidate.FrozenNodeId,
                newReport.Imports.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray(),
                newInput,
                candidate.PrerequisiteFrozenNodeIds,
                candidate.StatementId,
                candidate.WitnessId,
                oldReport.Declarations.SelectMany(static declaration => declaration.Axioms)
                    .Distinct(StringComparer.Ordinal)
                    .Order(StringComparer.Ordinal)
                    .ToImmutableArray(),
                active.Material.FrozenNodeId,
                oldReport.Imports.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray(),
                oldInput,
                active.Material.PrerequisiteFrozenNodeIds,
                active.Material.StatementId,
                active.Material.WitnessId,
                active.LastAttestationEventHash,
                "sha256:" + Convert.ToHexStringLower(SHA256.HashData(
                    Encoding.UTF8.GetBytes(fixture.Files[modulePath.Value]))));
            var element = FrozenLedgerCanonicalWriter.EnvironmentRecoordinateElement(payload);
            var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
                FrozenLedger.EnvironmentRecoordinateEventType,
                element);
            var identity = FrozenLedgerCanonicalWriter.EventIdentity(
                FrozenLedger.EnvironmentRecoordinateEventType,
                element,
                encoded.Hash);
            var path = FrozenLedgerChangeClassifier.AcceptedPath(identity);
            fixture.Files[path] = Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
            if (modulePath.Value == RuleFixture.RingPath)
            {
                ringEventPath = path;
            }
        }

        Assert.NotNull(ringEventPath);
        return ringEventPath;
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
}
