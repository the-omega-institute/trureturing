using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

// Added accepted-ledger events name Git objects as provenance anchors. ledger-append verifies
// them only on the producing machine, where a never-pushed commit still resolves; issue #1712
// froze entry 427ec58b onto commit b9e2a4aa that the remote disowned, and every other driver's
// ledger-append then failed closed. These tests pin the admission-side guard: `check` must
// validate the anchors of ADDED events (the admission clone holds only pushed objects) and must
// not re-validate the existing ledger on unrelated changes.
public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void CheckRetainsScopedStatementIdentityDetection()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = TrustedFrozenFixture();
        fixture.Files[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath]
            .Replace("Nat := 0", "Int := 0", StringComparison.Ordinal);
        fixture.Reports[RuleFixture.RingPath] = new LeanFileReport(
            [],
            [new LeanDeclaration("goldenRing", "def", "Int", [])]);
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
        Assert.Contains("statement identity changed", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains(
            "delta witness: " + RuleFixture.RingPath,
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void CheckRetainsScopedOutsideClosedCatalogDetection()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = TrustedFrozenFixture();
        fixture.Files.Remove(RuleFixture.RingPath);
        fixture.Reports.Remove(RuleFixture.RingPath);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.CreateWithKinds([(RuleFixture.RingPath, RawChangeKind.Deleted)]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var diagnostic = Assert.Single(
            rejected.Diagnostics.Where(static item => item.RuleId == RuleId.CreateKnown(8)));
        Assert.Equal(RuleFixture.RingPath, diagnostic.Path);
        Assert.Contains("outside the current Closed catalog", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains(
            "delta witness: " + RuleFixture.RingPath,
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008RejectsEmptyAddedRevokePayload()
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
            }));
        var path = FrozenLedgerChangeClassifier.AcceptedPath(encoded.Hash);
        fixture.Files[path] = System.Text.Encoding.UTF8.GetString(encoded.Bytes.AsSpan());
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
            "Revocation evidence is empty",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void CheckRejectsAddedLedgerEventWhoseAnchorDoesNotResolve()
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
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.CreateWithKinds(
                addedLedgerPaths.Select(static path => (path, RawChangeKind.Added))),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline),
            frozenReferenceValidator: static _ => throw new FrozenReferenceRejectionException(
                FrozenReferenceRejectionKind.MissingObject,
                $"frozen Git object git-sha1:{new string('a', 40)} is not a reachable commit"));
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["check", "--candidate-lean-report", WriteCandidateReport(temporary, fixture)],
            new ProductionCliEnvironment("/repo", gateway, new FakeLeanReportSource(null)),
            console);

        Assert.Equal(1, exitCode);
        Assert.Contains("SL-008", console.Output, StringComparison.Ordinal);
        Assert.Contains("is not a reachable commit", console.Output, StringComparison.Ordinal);
        Assert.Contains(addedLedgerPaths[0], console.Output, StringComparison.Ordinal);
        Assert.Contains("RULE_REJECTED", console.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("INFRASTRUCTURE_FAILURE", console.Output, StringComparison.Ordinal);
        Assert.Equal(string.Empty, console.Error);
    }

    [Fact]
    public void Sl008KeepsChangedFileScopeForAmbientDriftWhenEnvironmentPinsAreUnchanged()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = TrustedFrozenFixtureWithLedger(out _);
        fixture.Reports[RuleFixture.RingPath] = new LeanFileReport(
            [],
            [new LeanDeclaration("goldenRing", "def", "Int", [])]);
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create([]),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline));
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
    public void CheckRejectsAddedModuleWhoseFreezeCapturedAnEarlierBranchBlob()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = AddedFrozenRingFixture();
        var addedLedgerPaths = AddedLedgerPaths(fixture);
        Assert.Contains(AddedFreezePathFor(fixture, RuleFixture.RingPath), addedLedgerPaths);
        fixture.Files[RuleFixture.RingPath] += "\n-- changed after ledger-append\n";
        var changes = RawChangeSet.CreateWithKinds(
            new[] { (RuleFixture.RingPath, RawChangeKind.Added) }
                .Concat(addedLedgerPaths.Select(static path => (path, RawChangeKind.Added))));
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                changes,
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var frozenDiagnostics = rejected.Diagnostics
            .Where(static item => item.RuleId == RuleId.CreateKnown(8))
            .ToImmutableArray();
        Assert.True(
            frozenDiagnostics.Length == 1,
            string.Join('\n', rejected.Diagnostics.Select(static item => item.Render())));
        var diagnostic = frozenDiagnostics[0];
        Assert.True(
            diagnostic.Path == RuleFixture.RingPath,
            diagnostic.Render());
        Assert.Contains("does not match recomputed material", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains(
            AddedFreezePathFor(fixture, RuleFixture.RingPath),
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void Sl008ForcesFullScopeWhenCandidateProducerClosureOmitsItsOwnDefinition()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = TrustedFrozenFixtureWithLedger(out _);
        fixture.Reports[RuleFixture.RingPath] = new LeanFileReport(
            [],
            [new LeanDeclaration("goldenRing", "def", "Int", [])]);
        const string inputDefinition = "tools/scripts/report/lean-report-input.sh";
        var ledger = new ProductionFrozenLedgerAdmissionServices(
            "/repo",
            ImmutableHashSet<string>.Empty);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.CreateWithKinds([(inputDefinition, RawChangeKind.Modified)]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null),
            scribeEmissionVerifier: null,
            ledger);

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var diagnostic = Assert.Single(
            rejected.Diagnostics.Where(static item => item.RuleId == RuleId.CreateKnown(8)));
        Assert.Equal(RuleFixture.RingPath, diagnostic.Path);
        Assert.Contains("statement identity changed", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("delta witness: " + inputDefinition, diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal(1, ledger.IncrementalValidationCount);
    }

    [Fact]
    public void CheckRejectsFinalTreeWhenAnAddedFreezeWasDeletedWithinTheBranch()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = AddedFrozenRingFixture();
        var addedLedgerPath = AddedFreezePathFor(fixture, RuleFixture.RingPath);
        fixture.Files.Remove(addedLedgerPath);
        var changes = new[] { (RuleFixture.RingPath, RawChangeKind.Added) }
            .Concat(AddedLedgerPaths(fixture).Select(static path => (path, RawChangeKind.Added)));
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.CreateWithKinds(changes),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var diagnostic = Assert.Single(
            rejected.Diagnostics.Where(static item => item.RuleId == RuleId.CreateKnown(8)));
        Assert.Equal(RuleFixture.RingPath, diagnostic.Path);
        Assert.Contains("missing a Freeze event", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("ledger-append", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("delta witness: " + RuleFixture.RingPath, diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CheckDoesNotRunTheFinalLedgerGateForAnExistingRuleRejection()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        AddFrozenLedger(fixture);
        fixture.Apply("upward-import");
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create([RuleFixture.RingPath]),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline),
            currentRevisionResolver: static () => throw new InvalidOperationException(
                "final frozen-ledger gate must not run for an existing rule rejection"));
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        Assert.Contains(rejected.Diagnostics, item => item.RuleId == RuleId.CreateKnown(1));
        Assert.Equal(0, gateway.CurrentRevisionResolutionCount);
    }

    [Fact]
    public void CheckDoesNotResolveCurrentRevisionForAnUnrelatedChange()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        AddFrozenLedger(fixture);
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create([RuleFixture.BlueprintPath]),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline),
            currentRevisionResolver: static () => new FrozenRevisionIdentity(
                "candidate",
                "git-sha256:" + new string('a', 64),
                "git-sha256:" + new string('b', 64)));
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        Assert.IsType<AdmissionOutcome.Admitted>(outcome);
        Assert.Equal(0, gateway.CurrentRevisionResolutionCount);
    }

    [Fact]
    public void CheckDoesNotObserveCurrentRevisionFailureForAnUnrelatedChange()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        AddFrozenLedger(fixture);
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create([RuleFixture.BlueprintPath]),
            Snapshot(fixture.Files),
            Snapshot(fixture.Baseline),
            currentRevisionResolver: static () => throw new IOException(
                "current revision is unavailable"));
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        Assert.IsType<AdmissionOutcome.Admitted>(outcome);
        Assert.Equal(0, gateway.CurrentRevisionResolutionCount);
    }

    [Fact]
    public void UnrelatedProtectedChangeDoesNotAuthorizeLedgerReplay()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        AddFrozenLedger(fixture);
        var removedFreeze = FreezePathFor(fixture, RuleFixture.RingPath);
        fixture.Files.Remove(removedFreeze);
        const string scribePath = "Blueprint/D5/S0/Carrier/Ring.scribe.cs";
        fixture.Files[scribePath] = "// candidate Scribe definition\n";
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create([scribePath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        var protectedChange = Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(outcome);
        Assert.Contains(protectedChange.Sl022Diagnostics, item => item.RuleId == RuleId.CreateKnown(22));
    }

    [Fact]
    public void MergeFrozenLedgerRejectionRejectsVerificationRequiredOutsideItsCallerContract()
    {
        var diagnostic = new Diagnostic(
            RuleId.CreateKnown(22),
            "Conflict-of-interest gate",
            DisplaySeverity.Warning,
            AdmissionEffect.HumanGate,
            RuleFixture.SyntheticProtectedPath,
            "verification required");
        var original = new AdmissionOutcome.ProtectedSurfaceVerificationRequired(
            ImmutableArray.Create(diagnostic));
        var finalState = new AdmissionOutcome.RuleRejected(ImmutableArray.Create(diagnostic));

        Assert.Throws<InvalidOperationException>(() =>
            ProductionCliEnvironment.MergeFrozenLedgerRejection(original, finalState));
    }

    [Fact]
    public void MergeFrozenLedgerRejectionRejectsInfrastructureFailureOutsideItsCallerContract()
    {
        var original = new AdmissionOutcome.InfrastructureFailure(
            "original infrastructure failure with retained Lean/DAG context");
        var finalState = new AdmissionOutcome.RuleRejected(ImmutableArray.Create(new Diagnostic(
            RuleId.CreateKnown(8),
            "Frozen Hearts semantics",
            DisplaySeverity.Error,
            AdmissionEffect.Block,
            RuleFixture.RingPath,
            "later final-state rejection")));

        Assert.Throws<InvalidOperationException>(() =>
            ProductionCliEnvironment.MergeFrozenLedgerRejection(original, finalState));
    }

    private static string[] AddedLedgerPaths(RuleFixture fixture) =>
        fixture.Files.Keys
            .Where(FrozenLedgerChangeClassifier.IsAcceptedEventPath)
            .Where(path => !fixture.Baseline.ContainsKey(path))
            .Order(StringComparer.Ordinal)
            .ToArray();

    private static RuleFixture AddedFrozenRingFixture()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Baseline.Remove(RuleFixture.RingPath);
        fixture.BaselineReports.Remove(RuleFixture.RingPath);
        AddFrozenLedger(fixture);
        return fixture;
    }

    private static RuleFixture TrustedFrozenFixture()
    {
        return TrustedFrozenFixtureWithLedger(out _);
    }

    private static string AddedFreezePathFor(RuleFixture fixture, string nodePath) =>
        AddedLedgerPaths(fixture).Single(path =>
        {
            using var document = JsonDocument.Parse(fixture.Files[path]);
            var root = document.RootElement;
            return root.GetProperty("event_type").GetString() == "Freeze"
                && root.GetProperty("payload").GetProperty("input")
                    .GetProperty("descriptor_selector").GetString() == nodePath;
        });

    private static string FreezePathFor(RuleFixture fixture, string nodePath) =>
        fixture.Files.Single(item =>
        {
            if (!FrozenLedgerChangeClassifier.IsAcceptedEventPath(item.Key))
            {
                return false;
            }

            using var document = JsonDocument.Parse(item.Value);
            var root = document.RootElement;
            return root.GetProperty("event_type").GetString() == "Freeze"
                && root.GetProperty("payload").GetProperty("input")
                    .GetProperty("descriptor_selector").GetString() == nodePath;
        }).Key;

    private static string WriteCandidateReport(TemporaryDirectory temporary, RuleFixture fixture)
    {
        var candidateReport = Path.Combine(temporary.Path, "candidate.json");
        RawLeanReportArtifact.WriteFile(
            candidateReport,
            Decode(Snapshot(fixture.Files)),
            LeanAxiomReport.Create(fixture.Reports));
        return candidateReport;
    }
}
