using System.Collections.Immutable;
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
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        Assert.IsType<AdmissionOutcome.Admitted>(outcome);
        Assert.Equal(0, gateway.FrozenReferenceValidationCount);
    }

    [Fact]
    public void CheckAdmitsAddedLedgerEventsWhoseAnchorsResolve()
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
            Snapshot(fixture.Baseline));
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        Assert.IsType<AdmissionOutcome.Admitted>(outcome);
        // One validation per added event file, plus the whole-ledger validations that other
        // stages of check may legitimately run; the added-event scans are the ones whose
        // reference sets consist of exactly one input.
        var addedEventScans = gateway.FrozenReferenceValidations
            .Where(static references => references.Inputs.Length == 1)
            .ToImmutableArray();
        Assert.Equal(addedLedgerPaths.Length, addedEventScans.Length);
        Assert.All(
            addedEventScans,
            static references => Assert.Contains(
                FrozenLedgerTestData.GitOid('a'),
                references.CommitOids));
    }

    [Fact]
    public void CheckValidatesBothEnvironmentReferencesOfAnAddedRecoordinateEvent()
    {
        var (path, contents) = FrozenLedgerTests.EnvironmentRecoordinateDagEvent();
        FrozenLedgerReferenceSet? captured = null;
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.CreateWithKinds([(path, RawChangeKind.Added)]),
            Snapshot(new Dictionary<string, string>(StringComparer.Ordinal)
            {
                [path] = contents,
            }),
            baseline: null,
            frozenReferenceValidator: references =>
            {
                captured = references;
                throw new FrozenReferenceRejectionException(
                    FrozenReferenceRejectionKind.MissingObject,
                    "synthetic added EnvironmentRecoordinate anchor rejection");
            });
        var environment = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null));

        var outcome = environment.Check(["--candidate-lean-report", "unused.json"]);

        Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        Assert.NotNull(captured);
        Assert.Equal(2, captured.Inputs.Length);
        Assert.Equal(2, captured.EnvironmentReferences.Length);
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
    public void FinalLedgerGateFailsClosedWhenAdmittedEvaluationLacksReplayDependencies()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Baseline["Meta/registry.yaml"] = TestRegistry.Canonical;
        fixture.Files["Meta/domains.yaml"] = TestRegistry.Domains;
        fixture.Baseline["Meta/domains.yaml"] = TestRegistry.Domains;
        AddFrozenLedger(fixture);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.BlueprintPath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));
        var admitted = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);
        Assert.IsType<AdmissionOutcome.Admitted>(admitted);
        var validatorCalled = false;

        var outcome = ProductionCliEnvironment.ApplyFrozenLedgerFinalStateGate(
            new SnapshotAdmissionEvaluation(admitted, null, null),
            (_, _) =>
            {
                validatorCalled = true;
                return null;
            });

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("admitted evaluation lacks", failure.Message, StringComparison.Ordinal);
        Assert.False(validatorCalled);
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
        Assert.Equal(RuleFixture.RingPath, diagnostic.Path);
        Assert.Contains("material/blob drift", diagnostic.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("Reattest", diagnostic.Message, StringComparison.Ordinal);
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
        Assert.Contains("missing Freeze", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("ledger-sync", diagnostic.Message, StringComparison.Ordinal);
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
    public void CheckClassifiesFinalLedgerCatalogMismatchAsSl008()
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

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var diagnostic = Assert.Single(
            rejected.Diagnostics.Where(item => item.RuleId == RuleId.CreateKnown(8)));
        Assert.Contains("frozen Genesis", diagnostic.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(1, gateway.CurrentRevisionResolutionCount);
    }

    [Fact]
    public void CheckClassifiesFinalLedgerRepositoryResolutionFailureAsInfrastructure()
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

        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Equal("current revision is unavailable", failure.Message);
        Assert.Equal(1, gateway.CurrentRevisionResolutionCount);
    }

    [Fact]
    public void CheckMergesFinalLedgerDiagnosticsIntoProtectedSurfaceDiagnostics()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        AddFrozenLedger(fixture);
        var removedFreeze = FreezePathFor(fixture, RuleFixture.RingPath);
        fixture.Files.Remove(removedFreeze);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.SyntheticProtectedPath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));

        var outcome = environment.Check(
            ["--candidate-lean-report", WriteCandidateReport(temporary, fixture)]);

        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        Assert.Contains(rejected.Diagnostics, item => item.RuleId == RuleId.CreateKnown(22));
        Assert.Contains(
            rejected.Diagnostics,
            item => item.RuleId == RuleId.CreateKnown(8)
                && item.Path == RuleFixture.RingPath
                && item.Message.Contains("missing Freeze", StringComparison.Ordinal));
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

    private static string AddedFreezePathFor(RuleFixture fixture, string nodePath) =>
        AddedLedgerPaths(fixture).Single(path =>
        {
            using var document = JsonDocument.Parse(fixture.Files[path]);
            var root = document.RootElement;
            return root.GetProperty("event_type").GetString() == "Freeze"
                && root.GetProperty("payload").GetProperty("node_path").GetString() == nodePath;
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
                && root.GetProperty("payload").GetProperty("node_path").GetString() == nodePath;
        }).Key;

    private static string WriteCandidateReport(TemporaryDirectory temporary, RuleFixture fixture)
    {
        var candidateReport = Path.Combine(temporary.Path, "candidate.json");
        File.WriteAllBytes(
            candidateReport,
            RawLeanReportArtifact.Write(
                Decode(Snapshot(fixture.Files)),
                LeanAxiomReport.Create(fixture.Reports)).AsSpan());
        return candidateReport;
    }
}
