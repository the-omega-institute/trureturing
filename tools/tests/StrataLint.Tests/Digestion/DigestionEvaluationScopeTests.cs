using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;

namespace StrataLint.Tests;

public sealed class DigestionEvaluationScopeTests
{
    [Fact]
    public void EmptyChangeSetRetainsWholeTreeDiagnostics()
    {
        var scope = DigestionEvaluationScopes.ForChanges(
            RawChangeSet.Create(Array.Empty<string>()),
            "tools/StrataLint.Cli/Commands/DigestStatusCommand.cs");

        Assert.Equal(DigestionEvaluationScope.FullScan, scope);
    }

    [Fact]
    public void IngestScopePartialOnlyDeltaTriggersFullScan()
    {
        var scope = DigestionEvaluationScopes.ForChanges(
            RawChangeSet.Create(
                ["tools/StrataLint.Cli/Commands/Digestion/IngestCommand.Scope.cs"]),
            "tools/StrataLint.Cli/Commands/Digestion/IngestCommand.cs");

        Assert.Equal(DigestionEvaluationScope.FullScan, scope);
    }

    [Fact]
    public void NewCallerPartialAutomaticallyEntersImplementationDirectoryClosure()
    {
        var scope = DigestionEvaluationScopes.ForChanges(
            RawChangeSet.Create(
                ["tools/StrataLint.Cli/Commands/Digestion/IngestCommand.FuturePartial.cs"]),
            "tools/StrataLint.Cli/Commands/Digestion/IngestCommand.cs");

        Assert.Equal(DigestionEvaluationScope.FullScan, scope);
    }

    [Fact]
    public void ChangedSetDoesNotReplayProjectedStatusForAnUnchangedEntry()
    {
        var evaluation = EvaluateMismatchedProjectedStatus(
            RawChangeSet.Create(["notes/r16-unrelated.txt"]),
            DigestionEvaluationScope.ChangedSet);

        Assert.DoesNotContain(
            evaluation.Findings,
            static finding => finding.Contains("handwritten status", StringComparison.Ordinal));
    }

    [Fact]
    public void ChangedEntryStillValidatesProjectedStatus()
    {
        var evaluation = EvaluateMismatchedProjectedStatus(
            RawChangeSet.Create([BackfillInventoryLoader.RelativePath]),
            DigestionEvaluationScope.ChangedSet);

        Assert.Contains(
            evaluation.Findings,
            static finding => finding.Contains("handwritten status", StringComparison.Ordinal));
    }

    [Fact]
    public void ExplicitFullScanStillValidatesProjectedStatus()
    {
        var changes = RawChangeSet.Create(
            ["tools/StrataLint.Engine/Digestion/Evaluation/DigestionStatusEvaluator.cs"]);
        var scope = DigestionEvaluationScopes.ForChanges(
            changes,
            "tools/StrataLint.Cli/Commands/TheoryGeneration/TheoryCandidatesCommand.cs");
        var evaluation = EvaluateMismatchedProjectedStatus(changes, scope);

        Assert.Equal(DigestionEvaluationScope.FullScan, scope);
        Assert.Contains(
            evaluation.Findings,
            static finding => finding.Contains("handwritten status", StringComparison.Ordinal));
    }

    [Fact]
    public void ExplicitFullScanStillValidatesHistoricalCoverageReceipts()
    {
        var changes = RawChangeSet.Create(
            ["tools/StrataLint.Engine/Digestion/Evaluation/DigestionStatusEvaluator.cs"]);
        var scope = DigestionEvaluationScopes.ForChanges(
            changes,
            "tools/StrataLint.Cli/Commands/DigestStatusCommand.cs");
        var evaluation = EvaluateMismatchedCoverageReceipt(changes, scope);

        Assert.Equal(DigestionEvaluationScope.FullScan, scope);
        Assert.Contains(
            evaluation.Entries.Single().Gaps,
            static gap => gap.Code == "coverage-receipt-mismatch");
    }

    [Fact]
    public void ExplicitFullScanStillValidatesCasIntegrity()
    {
        var changes = RawChangeSet.Create(
            ["tools/StrataLint.Engine/Digestion/Evaluation/DigestionStatusEvaluator.cs"]);
        var scope = DigestionEvaluationScopes.ForChanges(
            changes,
            "tools/StrataLint.Cli/Commands/DigestStatusCommand.cs");
        var sourceBytes = Encoding.UTF8.GetBytes("manual full scan CAS\n");
        var atom = Atom("manual/full-scan-cas", sourceBytes);
        var document = Ledger(
            atom,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed,
            includeCoverageGid: false);
        var casPath = CasFile(atom).Path;
        var evaluation = DigestionStatusEvaluator.Evaluate(
            scope,
            document,
            Snapshot(
                ("docs/source.md", sourceBytes),
                (casPath, Encoding.UTF8.GetBytes("tampered committed CAS\n"))),
            AcceptedLean(Array.Empty<string>()),
            changes: changes);

        Assert.Equal(DigestionEvaluationScope.FullScan, scope);
        Assert.Contains(
            evaluation.Findings,
            finding => finding.Contains("CAS blob hash mismatch", StringComparison.Ordinal));
    }

    [Fact]
    public void ChangedSetRejectsAFullScanCasEvaluation()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("scope-bound CAS\n");
        var atom = Atom("manual/scope-bound-cas", sourceBytes);
        var document = Ledger(
            atom,
            DigestionMigrationState.Residual,
            DigestionTruthState.Open,
            includeCoverageGid: false);
        var snapshot = Snapshot(("docs/source.md", sourceBytes), CasFile(atom));
        var fullScanCas = DigestionCasStore.Evaluate(document, snapshot);
        var changes = RawChangeSet.Create(["notes/r17-unrelated-scope.txt"]);

        var exception = Assert.Throws<ArgumentException>(() =>
            DigestionStatusEvaluator.Evaluate(
                DigestionEvaluationScope.ChangedSet,
                document,
                snapshot,
                AcceptedLean(Array.Empty<string>()),
                casEvaluation: fullScanCas,
                changes: changes));

        Assert.Contains("CAS evaluation scope does not match", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ChangedCoverageTargetStillValidatesHistoricalCoverageReceipt()
    {
        var evaluation = EvaluateMismatchedCoverageReceipt(
            RawChangeSet.Create(["D5/S0/Carrier/FullScan.lean"]),
            DigestionEvaluationScope.ChangedSet);

        Assert.Contains(
            evaluation.Entries.Single().Gaps,
            static gap => gap.Code == "coverage-receipt-mismatch");
    }

    [Fact]
    public void UnrelatedChangeDoesNotValidateHistoricalCoverageReceipt()
    {
        var evaluation = EvaluateMismatchedCoverageReceipt(
            RawChangeSet.Create(["notes/r16-unrelated.txt"]),
            DigestionEvaluationScope.ChangedSet);

        Assert.DoesNotContain(
            evaluation.Entries.Single().Gaps,
            static gap => gap.Code == "coverage-receipt-mismatch");
    }

    private static DigestionLedgerEvaluation EvaluateMismatchedProjectedStatus(
        RawChangeSet changes,
        DigestionEvaluationScope scope)
    {
        var sourceBytes = Encoding.UTF8.GetBytes("manual changed-set status\n");
        var atom = Atom("manual/changed-set-status", sourceBytes);
        var document = Ledger(
            atom,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed,
            includeCoverageGid: false);
        return DigestionStatusEvaluator.Evaluate(
            scope,
            document,
            Snapshot(("docs/source.md", sourceBytes), CasFile(atom)),
            AcceptedLean(Array.Empty<string>()),
            changes: changes);
    }

    private static DigestionLedgerEvaluation EvaluateMismatchedCoverageReceipt(
        RawChangeSet changes,
        DigestionEvaluationScope scope)
    {
        var sourceBytes = Encoding.UTF8.GetBytes("manual full scan receipt\n");
        var atom = Atom("manual/full-scan", sourceBytes);
        const string gid = "D5/S0/Carrier/FullScan";
        const string targetPath = "D5/S0/Carrier/FullScan.lean";
        var target = Encoding.UTF8.GetBytes(Lean(gid));
        var document = Ledger(
            atom,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed,
            gid,
            new DigestionCoverageReceipt(
                gid,
                atom.Fingerprints.RawSha256,
                "sha256:0000000000000000000000000000000000000000000000000000000000000000"));
        var snapshot = Snapshot([
            (targetPath, target),
            CasFile(atom),
            ("docs/source.md", sourceBytes),
            .. FrozenStatementReceiptTestData.LedgerFiles(
                new FrozenStatementReceiptTestData.Module(
                    targetPath,
                    FrozenStatementReceiptTestData.Id('a'),
                    [])),
        ]);
        return DigestionStatusEvaluator.Evaluate(
            scope,
            document,
            snapshot,
            AcceptedLean(targetPath),
            baselineDocument: document,
            changes: changes);
    }

    private static BackfillInventoryDocument Ledger(
        DigestionAtom atom,
        DigestionMigrationState migration,
        DigestionTruthState truth,
        string coverageGid = "D5/X_Frontier/Probe",
        DigestionCoverageReceipt? coverageReceipt = null,
        bool includeCoverageGid = true)
    {
        var receipts = new DigestionReceipts(
            coverageReceipt is null ? [] : [coverageReceipt],
            [],
            [],
            [],
            null);
        var entry = DigestionTestSupport.Entry(
            atom,
            "scope-probe",
            AtomizerRegistry.NoAtomizerId,
            migration,
            truth,
            includeCoverageGid ? [coverageGid] : [],
            receipts,
            includeBoundary: false,
            sourceId: "scope-probe");
        return DigestionTestSupport.Document(
            AtomizerRegistry.NoAtomizerId,
            [entry],
            sourceId: "scope-probe");
    }

    private static DigestionAtom Atom(string astPath, byte[] bytes) => new(
        astPath,
        0,
        bytes.Length,
        ImmutableArray.CreateRange(bytes),
        DigestionFingerprint.Compute(bytes),
        ImmutableArray<DigestionContext>.Empty);
}
