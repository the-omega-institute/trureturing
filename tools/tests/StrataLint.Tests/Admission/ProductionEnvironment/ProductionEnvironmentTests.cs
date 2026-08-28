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
    public void CheckAdmitsAnUnrelatedChangeWhenMaterialArchiveIsMissingAndUnused()
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
            RawChangeSet.Create([RuleFixture.BlueprintPath]),
            currentRaw,
            baselineRaw);
        var ledger = new ProductionFrozenLedgerAdmissionServices(
            "/repo",
            ImmutableHashSet<string>.Empty);
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
            scribeEmissionVerifier: null,
            ledger);

        var outcome = environment.Check([
            "--candidate-lean-report", candidateReport,
        ]);

        Assert.IsType<AdmissionOutcome.Admitted>(outcome);
        Assert.Equal(0, ledger.BaseViewReadCount);
        Assert.Equal(0, ledger.DeltaEventLoadCount);
        Assert.Equal(0, ledger.AdmissionCatalogBuildCount);
        Assert.Equal(0, ledger.IncrementalValidationCount);
        Assert.Equal(0, gateway.CurrentRevisionResolutionCount);
        Assert.Equal(0, gateway.FrozenReferenceValidationCount);
    }

    [Fact]
    public void CheckPerformsScopedLedgerCallsForAManagedLeanDelta()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = TrustedFrozenFixture();
        var currentRaw = Snapshot(fixture.Files);
        var baselineRaw = Snapshot(fixture.Baseline);
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.CreateWithKinds([(RuleFixture.RingPath, RawChangeKind.Modified)]),
            currentRaw,
            baselineRaw);
        var ledger = new ProductionFrozenLedgerAdmissionServices(
            "/repo",
            ImmutableHashSet<string>.Empty);
        var candidateReport = Path.Combine(temporary.Path, "candidate.json");
        RawLeanReportArtifact.WriteFile(
            candidateReport,
            Decode(currentRaw),
            LeanAxiomReport.Create(fixture.Reports));
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null),
            scribeEmissionVerifier: null,
            ledger);

        var outcome = environment.Check([
            "--candidate-lean-report", candidateReport,
        ]);

        Assert.IsType<AdmissionOutcome.Admitted>(outcome);
        Assert.Equal(1, ledger.BaseViewReadCount);
        Assert.Equal(0, ledger.DeltaEventLoadCount);
        Assert.Equal(1, ledger.AdmissionCatalogBuildCount);
        Assert.Equal(1, ledger.IncrementalValidationCount);
        Assert.Equal(1, gateway.CurrentRevisionResolutionCount);
        Assert.Equal(0, gateway.FrozenReferenceValidationCount);
    }

    [Fact]
    public void CheckMapsUndecodableBoundaryToSl016RuleRejection()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var baselineBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var atom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, baselineBytes, DigestionTestSupport.Rules).Claims);
        var inserted = Encoding.UTF8.GetBytes("界");
        var currentBytes = baselineBytes[..(atom.EndByte - 1)]
            .Concat(inserted)
            .Concat(baselineBytes[(atom.EndByte - 1)..])
            .ToArray();
        var ledger = BoundaryIngestLedger(AtomizerRegistry.NoAtomizerId, atom);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(baselineBytes);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Files, ledger);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Baseline, ledger);
        fixture.Files.Remove(RuleFixture.FixtureCasPath);
        fixture.Baseline.Remove(RuleFixture.FixtureCasPath);
        fixture.Files[captured.RelativePath] = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
        fixture.Baseline[captured.RelativePath] = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
        var currentRaw = Snapshot(fixture.Files);
        var baselineRaw = Snapshot(fixture.Baseline);
        var candidateReport = Path.Combine(temporary.Path, "candidate.json");
        RawLeanReportArtifact.WriteFile(
            candidateReport,
            Decode(currentRaw),
            LeanAxiomReport.Create(fixture.Reports));
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath]),
                currentRaw,
                baselineRaw),
            new FakeLeanReportSource(null));
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            [
                "check",
                "--candidate-lean-report", candidateReport,
            ],
            environment,
            console);

        Assert.Equal(1, exitCode);
        Assert.Contains("SL-016", console.Output, StringComparison.Ordinal);
        Assert.Contains("run make ingest", console.Output, StringComparison.Ordinal);
        Assert.Contains("RULE_REJECTED", console.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("INFRASTRUCTURE_FAILURE", console.Output, StringComparison.Ordinal);
        Assert.Equal(string.Empty, console.Error);
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
    public void CheckMapsTruthDagCyclesToSl001BeforeRuleCatalog()
    {
        const string loopPath = "D5/S0/Carrier/Loop.lean";
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Baseline["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Files["Meta/domains.yaml"] = TestRegistry.Domains;
        fixture.Baseline["Meta/domains.yaml"] = TestRegistry.Domains;
        AddFrozenLedger(fixture);
        fixture.Files[loopPath] = "def loop : Nat := 0\n";
        fixture.Reports[RuleFixture.RingPath] = new LeanFileReport(
            ImmutableArray.Create("D5.S0.Carrier.Loop"),
            ImmutableArray<LeanDeclaration>.Empty);
        fixture.Reports[loopPath] = new LeanFileReport(
            ImmutableArray.Create("D5.S0.Carrier.Ring"),
            ImmutableArray<LeanDeclaration>.Empty);
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create(new[]
            {
                RuleFixture.SyntheticProtectedPath,
                RuleFixture.BlueprintPath,
            }),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
        var source = new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports));
        var environment = new ProductionCliEnvironment("/repo", gateway, source);

        var outcome = CheckWithReports(environment, fixture);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var meta = Assert.Single(
            rejected.Diagnostics.Where(item => item.RuleId == RuleId.CreateKnown(22)));
        Assert.DoesNotContain(
            rejected.Diagnostics,
            item => item.RuleId == RuleId.CreateKnown(1));
        Assert.NotEmpty(
            rejected.Diagnostics.Where(item => item.RuleId == RuleId.CreateKnown(8)));
        Assert.Equal(RuleFixture.SyntheticProtectedPath, meta.Path);
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
    }

    private static RawRepositorySnapshot Snapshot(IReadOnlyDictionary<string, string> files) =>
        RawRepositorySnapshot.Create(files.Select(pair => new RawRepositoryEntry(
            pair.Key,
            ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(pair.Value)),
            FrozenLedgerTestData.GitBlobOid(pair.Value))));

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
        var environment = new FrozenEnvironmentAttestation(
            FrozenLedgerTestData.GitOid('a'),
            FrozenLedgerTestData.GitOid('b'),
            FrozenLedgerTestData.GitBlobOid(toolchain),
            FrozenLedgerTestData.GitBlobOid(manifest))
        {
            LakefilePath = "lakefile.toml",
            LakefileBlobOid = FrozenLedgerTestData.GitBlobOid(lakefile),
        };
        var baselineCatalog = Catalog(fixture.Baseline, fixture.BaselineReports, environment);
        var currentCatalog = Catalog(fixture.Files, fixture.Reports, environment);
        var baselineEvents = FrozenLedgerTestData.EventFiles(baselineCatalog);
        var baselineCapability = FrozenLedgerTestData.Baseline(baselineCatalog);
        var currentEvents = baselineEvents.AddRange(DagLedgerAppendWriter.BuildNewEventFiles(
            FrozenLedgerGenerator.MissingFreezes(
            baselineCapability,
            currentCatalog)));
        SetLedger(fixture.Files, currentEvents);
        SetLedger(fixture.Baseline, baselineEvents);
        return baselineCapability;

        static FrozenMaterialCatalog Catalog(
            IReadOnlyDictionary<string, string> files,
            IReadOnlyDictionary<string, LeanFileReport> reports,
            FrozenEnvironmentAttestation environment)
        {
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(Snapshot(files))).Snapshot;
            var closure = Assert.IsType<LeanValidationOutcome.Accepted>(
                LeanClosureValidator.Validate(snapshot, LeanAxiomReport.Create(reports))).Capability;
            var states = LeanTruthStates.Resolve(snapshot, closure);
            var adjacency = LeanImportAdjacency.Build(snapshot, closure);
            var attestations = states
                .Where(static item => item.Value is TruthState.Closed)
                .Select(item => new FrozenModuleAttestation(
                    item.Key,
                    FrozenLedgerTestData.GitBlobOid(files[item.Key.Value])));
            return Assert.IsType<FrozenMaterialOutcome.Accepted>(
                FrozenContentAddress.Build(snapshot, closure, states, adjacency, environment, attestations)).Capability;
        }
    }

}

internal sealed class FakeRepositoryGateway(
    RawChangeSet changes,
    RawRepositorySnapshot? current,
    RawRepositorySnapshot? baseline,
    Func<FrozenLedgerReferenceSet, TrustedFrozenGitReferences>? frozenReferenceValidator = null,
    Func<FrozenRevisionIdentity>? currentRevisionResolver = null,
    Func<string, RawChangeSet>? changesForBase = null,
    RawRepositorySnapshot? forkPoint = null,
    Func<RawRepositorySnapshot>? currentReader = null)
    : IRepositoryGateway
{
    internal int ReadCount { get; private set; }

    internal int ReadCurrentCount { get; private set; }

    internal List<string> ReadRevisionCalls { get; } = [];

    internal List<FrozenLedgerInput> EnvironmentPinBlobReads { get; } = [];

    internal List<string> ReadChangesCalls { get; } = [];

    internal List<FrozenLedgerReferenceSet> FrozenReferenceValidations { get; } = [];

    internal int FrozenReferenceValidationCount => FrozenReferenceValidations.Count;

    internal int CurrentRevisionResolutionCount { get; private set; }

    public AdmissionTopologyOutcome InspectAdmissionTopology() =>
        throw new InvalidOperationException("topology should not be inspected");

    public PreparedRepository Prepare(string? protectedBase) => new(
        "baseline",
        forkPoint is null ? "baseline" : "fork",
        changes);

    public FrozenRevisionIdentity ResolveFrozenRevision(string revision)
    {
        var algorithm = revision.Length == 40 ? "git-sha1:" : "git-sha256:";
        return new FrozenRevisionIdentity(
            revision,
            algorithm + revision,
            algorithm + new string('b', revision.Length));
    }

    public FrozenRevisionIdentity ResolveCurrentRevision()
    {
        CurrentRevisionResolutionCount++;
        return currentRevisionResolver?.Invoke()
            ?? ResolveFrozenRevision(new string('a', 40));
    }

    public RawRepositorySnapshot ReadCurrent()
    {
        ReadCount++;
        ReadCurrentCount++;
        return WithAtomizerData(
            currentReader?.Invoke()
            ?? current
            ?? throw new InvalidOperationException("current snapshot should not be read"));
    }

    public RawRepositorySnapshot ReadRevision(string revision)
    {
        ReadCount++;
        ReadRevisionCalls.Add(revision);
        if (string.Equals(revision, "fork", StringComparison.Ordinal))
        {
            return WithAtomizerData(
                forkPoint ?? throw new InvalidOperationException("fork snapshot should not be read"));
        }

        return WithAtomizerData(
            baseline ?? throw new InvalidOperationException("baseline snapshot should not be read"));
    }

    public RawRepositorySnapshot ReadEnvironmentPinBlobs(FrozenLedgerInput input)
    {
        EnvironmentPinBlobReads.Add(input);
        if (input.SupportingBlobOids.Length != 2
            || input.SupportingBlobOids.Distinct(StringComparer.Ordinal).Count() != 2)
        {
            throw new InvalidOperationException(
                "protected semantic pins require exactly two distinct supporting blob OIDs");
        }

        var pins = (baseline
                ?? throw new InvalidOperationException("protected semantic pin blobs should not be read"))
            .Entries
            .Where(static entry => entry.Path is "lake-manifest.json" or "lean-toolchain")
            .ToArray();
        var resolved = pins
            .Select(static entry => entry.GitBlobOid)
            .Where(static oid => oid is not null)
            .Cast<string>()
            .ToHashSet(StringComparer.Ordinal);
        if (pins.Length != 2
            || resolved.Count != 2
            || !resolved.SetEquals(input.SupportingBlobOids))
        {
            throw new InvalidOperationException(
                "protected supporting blob OIDs do not resolve to lean-toolchain and lake-manifest.json");
        }

        return RawRepositorySnapshot.Create(pins);
    }

    public RawChangeSet ReadCurrentChanges() => changes;

    public RawChangeSet ReadChanges(string changeBase)
    {
        ReadChangesCalls.Add(changeBase);
        return changesForBase?.Invoke(changeBase) ?? changes;
    }

    public TrustedFrozenGitReferences ValidateFrozenReferences(FrozenLedgerReferenceSet references)
    {
        FrozenReferenceValidations.Add(references);
        return frozenReferenceValidator?.Invoke(references)
            ?? TrustedFrozenGitReferences.CreateForTrustedAdapter(references.Inputs);
    }

    private static RawRepositorySnapshot WithAtomizerData(RawRepositorySnapshot snapshot) =>
        snapshot.Entries.Any(static entry => entry.Path == TheoryAtomizerDataLoader.DataPath)
            ? snapshot
            : RawRepositorySnapshot.Create(snapshot.Entries.Add(new RawRepositoryEntry(
                TheoryAtomizerDataLoader.DataPath,
                ImmutableArray.CreateRange(DigestionTestSupport.RulesBytes))));
}

internal sealed class FakeLeanReportSource(LeanAxiomReport? report) : ILeanReportSource
{
    internal int CallCount { get; private set; }

    public LeanAxiomReport Load(RepositorySnapshot snapshot)
    {
        CallCount++;
        return report ?? throw new InvalidOperationException("Lean report source should not be called");
    }
}

internal sealed class FakeScribeEmissionVerifier(VerifiedScribeEmissions? verification)
    : IScribeEmissionVerifier
{
    public VerifiedScribeEmissions Verify(
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        RawChangeSet? changes = null) =>
        verification
        ?? throw new InvalidOperationException("Scribe emission verification failed: synthetic");
}
