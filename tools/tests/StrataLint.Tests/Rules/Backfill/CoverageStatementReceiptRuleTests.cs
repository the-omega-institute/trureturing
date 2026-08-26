using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CoverageStatementReceiptRuleTests
{
    [Fact]
    public void BackfillInventoryRuleTreatsStatementIdDriftAsNewCoverageReceiptMismatch()
    {
        var previousStatementId = FrozenStatementReceiptTestData.Id('5');
        var baseline = CoverageStatementReceiptTests.Evaluate(
            "D5/S0/Carrier/StatementReceipt.target",
            previousStatementId,
            previousStatementId,
            FrozenStatementReceiptTestData.Id('6'),
            TargetSource());
        var current = CoverageStatementReceiptTests.Evaluate(
            "D5/S0/Carrier/StatementReceipt.target",
            previousStatementId,
            FrozenStatementReceiptTestData.Id('7'),
            FrozenStatementReceiptTestData.Id('6'),
            TargetSource());
        var baselineEntry = baseline.Entries.Single().Entry;
        var baselineDocument = DigestionTestSupport.Document(
            AtomizerRegistry.NoAtomizerId,
            [baselineEntry]);
        var baselineSnapshot = SnapshotWithStatement(previousStatementId);

        var finding = Assert.Single(BackfillInventoryRule.ClassifyReceiptIntegrityGaps(
            current,
            baselineDocument,
            baselineSnapshot));

        Assert.Equal(AdmissionEffect.Block, finding.Effect);
        Assert.Equal(
            "statement-receipt:coverage-receipt-mismatch:D5/S0/Carrier/StatementReceipt.target",
            finding.Message);
    }

    private static RepositorySnapshot SnapshotWithStatement(string statementId)
    {
        const string modulePath = "D5/S0/Carrier/StatementReceipt.lean";
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [modulePath] = TargetSource(),
        };
        FrozenStatementReceiptTestData.AddLedger(
            files,
            new FrozenStatementReceiptTestData.Module(
                modulePath,
                FrozenStatementReceiptTestData.Id('6'),
                [
                    new FrozenStatementReceiptTestData.Declaration("sibling", FrozenStatementReceiptTestData.Id('2')),
                    new FrozenStatementReceiptTestData.Declaration("target", statementId),
                ]));
        var raw = RawRepositorySnapshot.Create(files.Select(static item =>
            RawRepositoryEntry.FromText(item.Key, item.Value)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static string TargetSource() =>
        "theorem target : True := by trivial\ntheorem sibling : True := by trivial\n";
}
