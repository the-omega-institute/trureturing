using System.Collections.Immutable;
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

    private static string[] AddedLedgerPaths(RuleFixture fixture) =>
        fixture.Files.Keys
            .Where(FrozenLedgerChangeClassifier.IsAcceptedEventPath)
            .Where(path => !fixture.Baseline.ContainsKey(path))
            .Order(StringComparer.Ordinal)
            .ToArray();

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
