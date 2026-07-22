using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void RouteUsesTheRepositoryRegistryAndEmitsStableJson()
    {
        using var temporary = new TemporaryDirectory();
        WritePolicyFiles(temporary.Path, TestRegistry.Canonical, TestRegistry.Domains);
        WriteManifest(temporary.Path, ValidManifestJson);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), null, null),
            new FakeLeanReportSource(null));

        var result = environment.Route(new[] { "manifest.json" });

        Assert.Equal(new CommandResult(true, ExpectedRouteJson, string.Empty), result);
    }

    [Theory]
    [MemberData(nameof(InvalidRouteArgumentSequences))]
    public void RouteReturnsExactUsageForInvalidArgumentCounts(string[] arguments)
    {
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), null, null),
            new FakeLeanReportSource(null));

        var result = environment.Route(arguments);

        Assert.Equal(
            new CommandResult(false, string.Empty, "USAGE: StrataLint route MANIFEST|-\n"),
            result);
    }

    [Fact]
    public void RouteReturnsExactManifestLoadFailure()
    {
        using var temporary = new TemporaryDirectory();
        WritePolicyFiles(temporary.Path, TestRegistry.Canonical, TestRegistry.Domains);
        WriteManifest(temporary.Path, "{}\n");
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), null, null),
            new FakeLeanReportSource(null));

        var result = environment.Route(new[] { "manifest.json" });

        Assert.Equal(
            new CommandResult(
                false,
                string.Empty,
                "INFRASTRUCTURE_FAILURE manifest keys must be exactly: "
                + "artifact, domain, generality, module, plane, selector, tag, theory\n"),
            result);
    }

    [Fact]
    public void RouteReturnsExactPolicyRejection()
    {
        using var temporary = new TemporaryDirectory();
        WritePolicyFiles(temporary.Path, TestRegistry.Canonical, DomainsWithoutCarrier);
        WriteManifest(temporary.Path, ValidManifestJson);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), null, null),
            new FakeLeanReportSource(null));

        var result = environment.Route(new[] { "manifest.json" });

        Assert.Equal(
            new CommandResult(
                false,
                string.Empty,
                "SL-015 route: formal route requires a controlled domain\n"),
            result);
    }

    [Fact]
    public void RouteRejectsNonRepositoryRelativeManifestPathAsInfrastructureFailure()
    {
        using var temporary = new TemporaryDirectory();
        WritePolicyFiles(temporary.Path, TestRegistry.Canonical, TestRegistry.Domains);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), null, null),
            new FakeLeanReportSource(null));

        var result = environment.Route(new[] { "../manifest.json" });

        Assert.Equal(
            new CommandResult(
                false,
                string.Empty,
                "INFRASTRUCTURE_FAILURE manifest path must be repository-relative\n"),
            result);
    }

    [Fact]
    public void RouteTranslatesRegistryFailureToExactInfrastructureResult()
    {
        using var temporary = new TemporaryDirectory();
        var invalidRegistry = TestRegistry.Canonical.Replace(
            "schema_version: 1",
            "schema_version: 2",
            StringComparison.Ordinal);
        WritePolicyFiles(temporary.Path, invalidRegistry, TestRegistry.Domains);
        WriteManifest(temporary.Path, ValidManifestJson);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), null, null),
            new FakeLeanReportSource(null));

        var result = environment.Route(new[] { "manifest.json" });

        Assert.Equal(
            new CommandResult(
                false,
                string.Empty,
                "INFRASTRUCTURE_FAILURE Unknown registry schema_version; expected 1.\n"),
            result);
    }

    [Fact]
    public void RouteReadsManifestFromStandardInputInAnIsolatedProcess()
    {
        using var temporary = new TemporaryDirectory();
        WritePolicyFiles(temporary.Path, TestRegistry.Canonical, TestRegistry.Domains);
        var executable = Path.Combine(
            Path.GetDirectoryName(typeof(Program).Assembly.Location)!,
            OperatingSystem.IsWindows() ? "StrataLint.exe" : "StrataLint");

        var result = BoundedProcessRunner.Run(
            executable,
            new[] { "route", "-" },
            temporary.Path,
            TimeSpan.FromSeconds(60),
            16 * 1024,
            Encoding.UTF8.GetBytes(ValidManifestJson));

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(Encoding.UTF8.GetBytes(ExpectedRouteJson), result.StandardOutput);
        Assert.Empty(result.StandardError);
    }

    [Fact]
    public void SelfTestReturnsExactUsageWhenArgumentsAreSupplied()
    {
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), null, null),
            new FakeLeanReportSource(null));

        var result = environment.SelfTest(new[] { "unexpected" });

        Assert.Equal(
            new CommandResult(false, string.Empty, "USAGE: StrataLint selftest\n"),
            result);
    }

    [Fact]
    public void SelfTestIsByteStableAcrossTwoPasses()
    {
        using var temporary = new TemporaryDirectory();
        WritePolicyFiles(temporary.Path, TestRegistry.Canonical, TestRegistry.Domains);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), null, null),
            new FakeLeanReportSource(null));

        var first = environment.SelfTest(Array.Empty<string>());
        var second = environment.SelfTest(Array.Empty<string>());

        var expected = new CommandResult(true, ExpectedSelfTestOutput, string.Empty);
        Assert.Equal(expected, first);
        Assert.Equal(expected, second);
    }

    [Fact]
    public void SelfTestReturnsExactInvariantMismatchWhenProbeCannotRoute()
    {
        using var temporary = new TemporaryDirectory();
        WritePolicyFiles(temporary.Path, TestRegistry.Canonical, DomainsWithoutCarrier);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), null, null),
            new FakeLeanReportSource(null));

        var result = environment.SelfTest(Array.Empty<string>());

        Assert.Equal(
            new CommandResult(false, string.Empty, "SELFTEST FAIL invariant mismatch\n"),
            result);
    }

    [Fact]
    public void SelfTestTranslatesRegistryFailureToExactFailureResult()
    {
        using var temporary = new TemporaryDirectory();
        var invalidRegistry = TestRegistry.Canonical.Replace(
            "schema_version: 1",
            "schema_version: 2",
            StringComparison.Ordinal);
        WritePolicyFiles(temporary.Path, invalidRegistry, TestRegistry.Domains);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create(Array.Empty<string>()), null, null),
            new FakeLeanReportSource(null));

        var result = environment.SelfTest(Array.Empty<string>());

        Assert.Equal(
            new CommandResult(
                false,
                string.Empty,
                "SELFTEST FAIL Unknown registry schema_version; expected 1.\n"),
            result);
    }

    [Fact]
    public void DigestStatusReportsEveryEntryAndZeroCurrentlyDeletable()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.DigestStatus(["--json"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"entries_total\": 1", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"deletable_now\": 0", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"atom_id\": \"fixture-atom\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"code\": \"boundary-not-reproducible\"", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusResidualSummaryUsesMachineDerivedUnresolvedSubitemGaps()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[BackfillInventoryLoader.RelativePath] = fixture.Files[BackfillInventoryLoader.RelativePath]
            .Replace(
                "          unresolved_subitems: []",
                "          unresolved_subitems:\n            - zeta-residual\n            - alpha-residual",
                StringComparison.Ordinal);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.DigestStatus(["--residual-summary"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("- unresolved_subitems: 2", result.Output, StringComparison.Ordinal);
        Assert.Contains("- mother_residual_atom_ids: 1", result.Output, StringComparison.Ordinal);
        Assert.Contains("- `fixture-atom` (2)", result.Output, StringComparison.Ordinal);
        Assert.True(
            result.Output.IndexOf("`alpha-residual`", StringComparison.Ordinal)
                < result.Output.IndexOf("`zeta-residual`", StringComparison.Ordinal));
        Assert.DoesNotContain("boundary-not-reproducible", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusReportsHistoricalAndCurrentCasReceiptsAsSeen()
    {
        var fixture = new RuleFixture();
        var atomizerId = AtomizerRegistry.RegisteredIds[0];
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes).Claims);
        var baselineLedger = IngestLedger(atomizerId, oldAtom);
        var baselineDocument = BackfillInventoryLoader.Load(baselineLedger);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var planningSnapshot = Decode(Snapshot(new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes),
            [oldCapture.RelativePath] = Encoding.UTF8.GetString(oldCapture.Bytes.AsSpan()),
        }));
        var plan = DigestionIngestor.Plan(baselineDocument, planningSnapshot, baselineDocument);
        var candidateLedger = Encoding.UTF8.GetString(
            BackfillInventoryWriter.Write(plan.Document).AsSpan());
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        fixture.Files[BackfillInventoryLoader.RelativePath] = candidateLedger;
        fixture.Baseline[BackfillInventoryLoader.RelativePath] = baselineLedger;
        fixture.Files.Remove(GoldenCorpus.FixtureCasPath);
        fixture.Baseline.Remove(GoldenCorpus.FixtureCasPath);
        fixture.Files[oldCapture.RelativePath] = Encoding.UTF8.GetString(oldCapture.Bytes.AsSpan());
        fixture.Baseline[oldCapture.RelativePath] = Encoding.UTF8.GetString(oldCapture.Bytes.AsSpan());
        foreach (var item in plan.CasObjects)
        {
            fixture.Files[item.RelativePath] = Encoding.UTF8.GetString(item.Bytes.AsSpan());
        }

        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.DigestStatus(["--json", "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"alignment\": \"seen\"", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("stale-receipt-not-deletable", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusFailsClosedWhenProjectedStatusWasHandwrittenIncorrectly()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        const string expected = "          migration: partial\n          truth: closed";
        const string falseProjection = "          migration: absorbed\n          truth: closed";
        fixture.Files["Meta/BACKFILL.yaml"] = fixture.Files["Meta/BACKFILL.yaml"].Replace(
            expected,
            falseProjection,
            StringComparison.Ordinal);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.DigestStatus(Array.Empty<string>());

        Assert.False(result.Success);
        Assert.Contains("handwritten status", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusFailsClosedWhenScribeVerificationFails()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(null));

        var result = environment.DigestStatus(Array.Empty<string>());

        Assert.False(result.Success);
        Assert.Contains("Scribe emission verification failed", result.Error, StringComparison.Ordinal);
    }

    private static RawRepositorySnapshot Snapshot(IReadOnlyDictionary<string, string> files) =>
        RawRepositorySnapshot.Create(files.Select(pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));

    private static void WritePolicyFiles(string root, string registry, string domains)
    {
        Directory.CreateDirectory(Path.Combine(root, "Meta"));
        File.WriteAllText(
            Path.Combine(root, "Meta", "registry.yaml"),
            registry,
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(root, "Meta", "domains.yaml"),
            domains,
            new UTF8Encoding(false));
    }

    private static void WriteManifest(string root, string content) =>
        File.WriteAllText(
            Path.Combine(root, "manifest.json"),
            content,
            new UTF8Encoding(false));

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

    private static AdmissionOutcome CheckWithReports(
        ProductionCliEnvironment environment,
        RuleFixture fixture)
    {
        using var temporary = new TemporaryDirectory();
        var candidateReport = Path.Combine(temporary.Path, "candidate.json");
        var baselineReport = Path.Combine(temporary.Path, "baseline.json");
        File.WriteAllBytes(
            candidateReport,
            RawLeanReportArtifact.Write(
                Decode(Snapshot(fixture.Files)),
                LeanAxiomReport.Create(fixture.Reports)).AsSpan());
        File.WriteAllBytes(
            baselineReport,
            RawLeanReportArtifact.Write(
                Decode(Snapshot(fixture.Baseline)),
                LeanAxiomReport.Create(fixture.BaselineReports)).AsSpan());
        return environment.Check(new[]
        {
            "--candidate-lean-report", candidateReport,
            "--baseline-lean-report", baselineReport,
        });
    }

    private static (RepositorySnapshot Snapshot, AcceptedLeanClosure Lean, AcyclicTruthDag Dag) BuildState(
        IReadOnlyDictionary<string, string> files,
        IReadOnlyDictionary<string, LeanFileReport> reports)
    {
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(Snapshot(files))).Snapshot;
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(snapshot, LeanAxiomReport.Create(reports))).Capability;
        var dag = Assert.IsType<DagBuildOutcome.Accepted>(
            AcyclicTruthDag.Build(snapshot, lean)).Capability;
        return (snapshot, lean, dag);
    }

    private static void AddFrozenLedger(RuleFixture fixture)
    {
        const string toolchain = "leanprover/lean4:v4.24.0\n";
        const string manifest = "{}\n";
        fixture.Files["lean-toolchain"] = toolchain;
        fixture.Baseline["lean-toolchain"] = toolchain;
        fixture.Files["lake-manifest.json"] = manifest;
        fixture.Baseline["lake-manifest.json"] = manifest;
        var environment = new FrozenEnvironmentAttestation(
            FrozenLedgerTestData.GitOid('a'),
            FrozenLedgerTestData.GitOid('b'),
            FrozenLedgerTestData.GitBlobOid(toolchain),
            FrozenLedgerTestData.GitBlobOid(manifest));
        var baselineCatalog = Catalog(fixture.Baseline, fixture.BaselineReports, environment);
        var currentCatalog = Catalog(fixture.Files, fixture.Reports, environment);
        var baselineLedger = FrozenLedgerGenerator.GenerateGenesis(
            baselineCatalog,
            new FrozenGenesisDescriptor(
                FrozenLedgerTestData.GitOid('e'),
                RuleCatalog.Default.RootSha256));
        var baselineSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(baselineLedger.AsSpan())).Syntax;
        var baselineCapability = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            FrozenLedgerTestData.ValidateGenesis(baselineSyntax, baselineCatalog)).Capability;
        var currentLedger = FrozenLedgerGenerator.AppendMissingFreezes(
            baselineCapability,
            currentCatalog);
        fixture.Files[FrozenLedgerChangeClassifier.LedgerPath] = Encoding.UTF8.GetString(currentLedger.AsSpan());
        fixture.Baseline[FrozenLedgerChangeClassifier.LedgerPath] = Encoding.UTF8.GetString(baselineLedger.AsSpan());

        static FrozenMaterialCatalog Catalog(
            IReadOnlyDictionary<string, string> files,
            IReadOnlyDictionary<string, LeanFileReport> reports,
            FrozenEnvironmentAttestation environment)
        {
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(Snapshot(files))).Snapshot;
            var closure = Assert.IsType<LeanValidationOutcome.Accepted>(
                LeanClosureValidator.Validate(snapshot, LeanAxiomReport.Create(reports))).Capability;
            var dag = Assert.IsType<DagBuildOutcome.Accepted>(AcyclicTruthDag.Build(snapshot, closure)).Capability;
            var attestations = dag.Nodes
                .Where(static node => node.State is TruthState.Closed && node.ModuleName is not null)
                .Select(node => new FrozenModuleAttestation(
                    node.RepoPath,
                    FrozenLedgerTestData.GitBlobOid(files[node.RepoPath.Value])));
            return Assert.IsType<FrozenMaterialOutcome.Accepted>(
                FrozenContentAddress.Build(snapshot, closure, dag, environment, attestations)).Capability;
        }
    }
}

internal sealed class FakeRepositoryGateway(
    RawChangeSet changes,
    RawRepositorySnapshot? current,
    RawRepositorySnapshot? baseline) : IRepositoryGateway
{
    internal List<string?> PreparedBases { get; } = new();

    internal Exception? PrepareException { get; init; }

    internal int ReadCount { get; private set; }

    internal int FrozenReferenceValidationCount { get; private set; }

    public AdmissionTopologyOutcome InspectAdmissionTopology() =>
        throw new InvalidOperationException("topology should not be inspected");

    public PreparedRepository Prepare(string? protectedBase)
    {
        PreparedBases.Add(protectedBase);
        if (PrepareException is not null)
        {
            throw PrepareException;
        }

        return new PreparedRepository("baseline", changes);
    }

    public FrozenRevisionIdentity ResolveFrozenRevision(string revision)
    {
        var algorithm = revision.Length == 40 ? "git-sha1:" : "git-sha256:";
        return new FrozenRevisionIdentity(
            revision,
            algorithm + revision,
            algorithm + new string('b', revision.Length));
    }

    public FrozenRevisionIdentity ResolveCurrentRevision() =>
        ResolveFrozenRevision(new string('a', 40));

    public RawRepositorySnapshot ReadCurrent()
    {
        ReadCount++;
        return current ?? throw new InvalidOperationException("current snapshot should not be read");
    }

    public RawRepositorySnapshot ReadRevision(string revision)
    {
        ReadCount++;
        return baseline ?? throw new InvalidOperationException("baseline snapshot should not be read");
    }

    public RawRepositorySnapshot ReadFrozenRevision(string revision)
    {
        ReadCount++;
        return baseline ?? throw new InvalidOperationException("frozen revision snapshot should not be read");
    }

    public TrustedFrozenGitReferences ValidateFrozenReferences(FrozenLedgerReferenceSet references)
    {
        FrozenReferenceValidationCount++;
        return TrustedFrozenGitReferences.CreateForTrustedAdapter(references.Inputs);
    }
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
    public VerifiedScribeEmissions Verify(LeanAxiomReport report) =>
        verification ?? throw new InvalidOperationException("Scribe emission verification failed: synthetic");
}

internal sealed class TemporaryDirectory : IDisposable
{
    internal TemporaryDirectory()
    {
        Path = System.IO.Path.Combine(System.IO.Path.GetTempPath(), "stratalint-tests-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(Path);
    }

    internal string Path { get; }

    public void Dispose() => Directory.Delete(Path, recursive: true);
}
