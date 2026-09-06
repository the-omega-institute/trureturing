using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void CheckEvaluatesProtectedChangeContentAndReturnsStructuredMetaSignal()
    {
        var fixture = TrustedFrozenFixture();
        const string protectedPath = RuleFixture.SyntheticProtectedPath;
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create(new[] { protectedPath }),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
        var source = new FakeLeanReportSource(null);
        var environment = new ProductionCliEnvironment("/repo", gateway, source);

        var outcome = CheckWithReports(environment, fixture);

        Assert.True(
            outcome is AdmissionOutcome.ProtectedSurfaceChange,
            outcome switch
            {
                AdmissionOutcome.RuleRejected rejected => string.Join(
                    '\n',
                    rejected.Diagnostics.Select(static diagnostic => diagnostic.Render())),
                AdmissionOutcome.InfrastructureFailure failure => failure.Message,
                _ => outcome.GetType().FullName,
            });
        var protectedChange = (AdmissionOutcome.ProtectedSurfaceChange)outcome;
        AssertCompleteRuleDisposition(protectedChange.ContentCertificate);
        Assert.Contains(protectedChange.ChangeSet.Paths, item => item.Value == protectedPath);
        Assert.Contains(
            protectedChange.Sl022Diagnostics,
            item => item.RuleId == RuleId.CreateKnown(22)
                && item.Path == protectedPath
                && item.Message == "protected-surface change detected (SL-022)");
        Assert.Equal(2, gateway.ReadCount);
        Assert.Equal(0, source.CallCount);
    }

    [Fact]
    public void CheckRejectsProtectedChangeWhenContentViolatesSl001()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Apply("upward-import");
        const string protectedPath = RuleFixture.SyntheticProtectedPath;
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create(new[] { protectedPath, RuleFixture.RingPath }),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));

        var outcome = CheckWithReports(environment, fixture);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        Assert.Contains(rejected.Diagnostics, item => item.RuleId == RuleId.CreateKnown(1));
        Assert.Contains(rejected.Diagnostics, item => item.RuleId == RuleId.CreateKnown(22));
        Assert.Equal(2, gateway.ReadCount);
    }

    [Fact]
    public void CheckReturnsAdmittedForFullyCleanOrdinaryChange()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Baseline["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Files["Meta/domains.yaml"] = TestRegistry.Domains;
        fixture.Baseline["Meta/domains.yaml"] = TestRegistry.Domains;
        AddFrozenLedger(fixture);
        var currentRaw = Snapshot(fixture.Files);
        var baselineRaw = Snapshot(fixture.Baseline);
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create(new[] { RuleFixture.BlueprintPath }),
            currentRaw,
            baselineRaw);
        var candidateReport = Path.Combine(temporary.Path, "candidate.json");
        RawLeanReportArtifact.WriteFile(
            candidateReport,
            Decode(currentRaw),
            LeanAxiomReport.Create(fixture.Reports));
        var source = new FakeLeanReportSource(null);
        var environment = new ProductionCliEnvironment("/repo", gateway, source);

        var outcome = environment.Check(new[]
        {
            "--candidate-lean-report", candidateReport,
        });

        var admitted = Assert.IsType<AdmissionOutcome.Admitted>(outcome);
        AssertCompleteRuleDisposition(admitted.Certificate);
        Assert.Equal(2, gateway.ReadCount);
        Assert.Equal(0, source.CallCount);
    }

    [Fact]
    public void CheckAdmitsAnAddedAcceptedEventWithMatchingStatePinWithoutSidecarRead()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Baseline["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Files["Meta/domains.yaml"] = TestRegistry.Domains;
        fixture.Baseline["Meta/domains.yaml"] = TestRegistry.Domains;
        AddFrozenLedger(fixture);
        var addedEventPath = fixture.Files.Keys
            .First(FrozenLedgerChangeClassifier.IsAcceptedEventPath);
        var snapshotWithEvent = Decode(Snapshot(fixture.Files));
        var loaded = Assert.IsType<DagLedgerFilesLoadOutcome.Loaded>(
            FrozenAcceptedEventLoader.LoadFiles(
                [snapshotWithEvent.Files[RepoPath.CreateKnown(addedEventPath)]]));
        var statePath = FrozenStatePath.FromModulePath(
            Assert.Single(loaded.Events).DescriptorPath).Value;
        fixture.Baseline.Remove(addedEventPath);
        Assert.Contains(statePath, fixture.Files.Keys);
        var currentRaw = Snapshot(fixture.Files);
        var baselineRaw = Snapshot(fixture.Baseline);
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.CreateWithKinds([(addedEventPath, RawChangeKind.Added)]),
            currentRaw,
            baselineRaw);
        var candidateReport = Path.Combine(temporary.Path, "candidate.json");
        RawLeanReportArtifact.WriteFile(
            candidateReport,
            Decode(currentRaw),
            LeanAxiomReport.Create(fixture.Reports));
        File.Delete(RawLeanReportArtifact.MaterialsPath(candidateReport));
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null),
            scribeEmissionVerifier: null);

        var outcome = environment.Check([
            "--candidate-lean-report", candidateReport,
        ]);

        Assert.IsType<AdmissionOutcome.Admitted>(outcome);
        Assert.Equal(0, gateway.CurrentRevisionResolutionCount);
    }

    // --merge-base was an undocumented legacy alias of --protected-base; the
    // parser accepts the canonical spelling only (no compatibility shims).
    [Fact]
    public void CheckRejectsTheRetiredMergeBaseAlias()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create(new[] { RuleFixture.SyntheticProtectedPath }),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
        var source = new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports));
        var environment = new ProductionCliEnvironment("/repo", gateway, source);

        var outcome = environment.Check(new[]
        {
            "--merge-base", "0000000000000000000000000000000000000000",
            "--candidate-lean-report", "candidate.json",
        });

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("USAGE:", failure.Message, StringComparison.Ordinal);
        Assert.Equal(0, source.CallCount);
    }

    [Fact]
    // Admission consumes the candidate report only; the candidate report remains required.
    public void CheckRequiresThePrecomputedCandidateLeanReportForProtectedChanges()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Baseline["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Files["Meta/domains.yaml"] = TestRegistry.Domains;
        fixture.Baseline["Meta/domains.yaml"] = TestRegistry.Domains;
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create(new[] { RuleFixture.SyntheticProtectedPath }),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
        var source = new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports));
        var environment = new ProductionCliEnvironment("/repo", gateway, source);

        var outcome = environment.Check(Array.Empty<string>());

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("--candidate-lean-report", failure.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("--baseline-lean-report", failure.Message, StringComparison.Ordinal);
        Assert.Equal(0, source.CallCount);
    }

    [Fact]
    public void CheckRequiresCurrentProducerCapabilityForScribeDefinitionEvolution()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        AddFrozenLedger(fixture);
        const string scribePath = "Blueprint/D5/S0/Carrier/Ring.scribe.cs";
        fixture.Files[scribePath] = "// candidate Scribe definition\n";
        var current = Snapshot(fixture.Files);
        var baseline = Snapshot(fixture.Baseline);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([scribePath]),
                current,
                baseline),
            new FakeLeanReportSource(null),
            new FakeScribeEmissionVerifier(null));

        var outcome = CheckWithReports(environment, fixture);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("Scribe emission verification failed", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CheckRequiresCurrentProducerCapabilityForAnyProtectedChange()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = TrustedFrozenFixture();
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.SyntheticProtectedPath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null),
            new FakeScribeEmissionVerifier(null));

        var outcome = CheckWithReports(environment, fixture);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("Scribe emission verification failed", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CheckKeepsScribeVerifierMismatchHardForClearChanges()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        AddFrozenLedger(fixture);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.BlueprintPath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null),
            new FakeScribeEmissionVerifier(null));

        var outcome = CheckWithReports(environment, fixture);

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("Scribe emission verification failed", failure.Message, StringComparison.Ordinal);
    }
    [Fact]
    public void RouteUsesTheRepositoryRegistryAndEmitsStableJson()
    {
        using var temporary = new TemporaryDirectory();
        Directory.CreateDirectory(Path.Combine(temporary.Path, "Meta"));
        File.WriteAllText(Path.Combine(temporary.Path, "Meta", "registry.yaml"), TestRegistry.Canonical, new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(temporary.Path, "Meta", "domains.yaml"), TestRegistry.Domains, new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(temporary.Path, "manifest.json"),
            "{\"artifact\":\"lean\",\"domain\":\"Carrier\",\"generality\":\"G\",\"module\":\"Probe\",\"plane\":\"F\",\"selector\":\"\",\"tag\":\"\",\"theory\":\"D5\"}\n",
            new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(new Dictionary<string, string>()),
                null),
            new FakeLeanReportSource(null));

        var result = environment.Route(new[] { "manifest.json" });

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"gid\": \"D5/S0/Carrier/Probe\"", result.Output, StringComparison.Ordinal);
        Assert.EndsWith("\n", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void SelfTestIsByteStableAcrossTwoPasses()
    {
        var repositoryRoot = TestRepositoryLayout.FindRoot();
        var environment = new ProductionCliEnvironment(
            repositoryRoot,
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), null, null),
            new FakeLeanReportSource(null));

        var first = environment.SelfTest(Array.Empty<string>());
        var second = environment.SelfTest(Array.Empty<string>());

        Assert.True(first.Success, first.Error);
        Assert.True(second.Success, second.Error);
        Assert.Equal(first.Output, second.Output);
        Assert.Contains("SELFTEST PASS", first.Output, StringComparison.Ordinal);

        var snapshot = Decode(new GitRepositoryGateway(repositoryRoot).ReadCurrent());
        var report = new PrecomputedLeanReportSource(repositoryRoot).Load(snapshot);
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(snapshot, report)).Capability;
        var document = BackfillInventoryLoader.Load(snapshot);
        var changes = RawChangeSet.Create(["README.md"]);
        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            document,
            snapshot,
            lean,
            new ProductionScribeEmissionVerifier().Verify(snapshot, report),
            baselineDocument: document,
            baselineSnapshot: snapshot,
            changes: changes,
            projectedStatusChanges: changes,
            receiptGateChanges: changes);

        Assert.Equal(
            document.RequireDigestionEntries().Length,
            evaluation.Entries.Length);
        Assert.All(evaluation.Entries, static entry =>
            Assert.Equal(entry.Entry.ProjectedStatus, entry.DerivedStatus));
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

    private static AdmissionOutcome CheckWithReports(
        ProductionCliEnvironment environment,
        RuleFixture fixture)
    {
        using var temporary = new TemporaryDirectory();
        var candidateReport = Path.Combine(temporary.Path, "candidate.json");
        RawLeanReportArtifact.WriteFile(
            candidateReport,
            Decode(Snapshot(fixture.Files)),
            LeanAxiomReport.Create(fixture.Reports));
        return environment.Check(new[]
        {
            "--candidate-lean-report", candidateReport,
        });
    }

    private static void AssertCompleteRuleDisposition(AdmissionCertificate certificate)
    {
        var deferred = certificate.DeferredRules.Select(static item => item.RuleId).ToImmutableArray();
        Assert.NotEmpty(certificate.ExecutedRules);
        Assert.NotEmpty(certificate.SkippedRules);
        Assert.NotEmpty(deferred);
        Assert.Empty(certificate.ExecutedRules.Intersect(certificate.SkippedRules));
        Assert.Empty(certificate.ExecutedRules.Intersect(deferred));
        Assert.Empty(certificate.SkippedRules.Intersect(deferred));
        Assert.Equal(
            RuleCatalog.Default.Descriptors.Select(static item => item.Id)
                .OrderBy(static item => item.Value, StringComparer.Ordinal),
            certificate.ExecutedRules.Concat(certificate.SkippedRules).Concat(deferred)
                .OrderBy(static item => item.Value, StringComparer.Ordinal));
    }

    private static FrozenLedgerConsistent AddFrozenLedger(
        RuleFixture fixture,
        string manifest = "{}\n")
    {
        const string toolchain = "leanprover/lean4:v4.24.0\n";
        const string lakefile = "name = \"Fixture\"\n";
        fixture.Files["lean-toolchain"] = toolchain;
        fixture.Baseline["lean-toolchain"] = toolchain;
        fixture.Files["lakefile.toml"] = lakefile;
        fixture.Baseline["lakefile.toml"] = lakefile;
        fixture.Files["lake-manifest.json"] = manifest;
        fixture.Baseline["lake-manifest.json"] = manifest;
        var baselineCatalog = Catalog(fixture.Baseline, fixture.BaselineReports);
        var currentCatalog = Catalog(fixture.Files, fixture.Reports);
        var baselineEvents = FrozenLedgerTestData.EventFiles(baselineCatalog);
        var baselineCapability = FrozenLedgerTestData.Baseline(baselineCatalog);
        var currentEvents = FrozenLedgerTestData.EventFiles(currentCatalog);
        SetLedger(fixture.Files, currentEvents);
        SetLedger(fixture.Baseline, baselineEvents);
        return baselineCapability;

        static FrozenMaterialCatalog Catalog(
            IReadOnlyDictionary<string, string> files,
            IReadOnlyDictionary<string, LeanFileReport> reports)
        {
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(Snapshot(files))).Snapshot;
            var closure = Assert.IsType<LeanValidationOutcome.Accepted>(
                LeanClosureValidator.Validate(snapshot, LeanAxiomReport.Create(reports))).Capability;
            var states = LeanTruthStates.Resolve(snapshot, closure);
            var adjacency = LeanImportAdjacency.Build(snapshot, closure);
            return Assert.IsType<FrozenMaterialOutcome.Accepted>(
                FrozenContentAddress.Build(snapshot, closure, states, adjacency)).Capability;
        }
    }

    private static RuleFixture TrustedFrozenFixture()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        _ = AddFrozenLedger(fixture);
        SettleCurrentCoverage(fixture);
        var settled = BackfillInventoryLoader.Load(Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(Snapshot(fixture.Files))).Snapshot);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Baseline, settled);
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

    private static void SettleCurrentCoverage(RuleFixture fixture)
    {
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(Snapshot(fixture.Files))).Snapshot;
        var lean = AcceptedLeanClosure.Create(LeanAxiomReport.Create(fixture.Reports));
        var truthStates = LeanTruthStates.Resolve(snapshot, lean);
        var aligned = DigestionCoverageTargetAligner.Align(
            BackfillInventoryLoader.Load(snapshot),
            snapshot,
            lean,
            truthStates);
        var statusByAtomId = DigestionStatusEvaluator.Evaluate(
                DigestionEvaluationScope.FullScan,
                aligned,
                snapshot,
                lean,
                truthStates: truthStates)
            .Entries
            .ToDictionary(
                static entry => entry.Entry.AtomId,
                static entry => entry.DerivedStatus,
                StringComparer.Ordinal);
        var settled = aligned.WithDigestionSources(aligned.RequireDigestionSources()
            .Select(source => source with
            {
                Entries = source.Entries.Select(entry => entry with
                {
                    ProjectedStatus = statusByAtomId[entry.AtomId],
                }).ToImmutableArray(),
            }).ToImmutableArray());
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Files, settled);
    }

}
