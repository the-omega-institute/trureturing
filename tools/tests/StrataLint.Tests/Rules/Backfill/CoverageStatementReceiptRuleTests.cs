using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CoverageStatementReceiptRuleTests
{
    [Fact]
    public void FrozenLedgerEventChangeWakesSl016()
    {
        var path = FrozenLedgerChangeClassifier.AcceptedRoot + "/changed.json";
        var context = new RuleFixture().Build(RawChangeSet.Create([path]));

        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
    }

    [Fact]
    public void StatementIdDriftIsANewBlockingCoverageReceiptMismatch()
    {
        const string gid = "D5/S0/Carrier/StatementReceipt.target";
        var targetSource = "theorem target : True := by trivial\n";
        var previousStatementId = DigestionFingerprint.Compute(
            System.Text.Encoding.UTF8.GetBytes(targetSource)).RawSha256;
        var current = CoverageStatementReceiptTests.Evaluate(
            gid,
            previousStatementId,
            FrozenStatementReceiptTestData.Id('7'),
            FrozenStatementReceiptTestData.Id('6'),
            targetSource);

        var finding = Assert.Single(BackfillInventoryRule.ClassifyReceiptIntegrityGaps(current));

        Assert.Equal(AdmissionEffect.Block, finding.Effect);
        Assert.Equal(
            "statement-receipt:coverage-receipt-mismatch:D5/S0/Carrier/StatementReceipt.target",
            finding.Message);
    }

}
