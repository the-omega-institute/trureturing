using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

// align-scribe 多对事务(#3297)的专项测试;主文件保留单对与 cover 事务用例。
public sealed partial class ProductionEnvironmentTests
{
    [Theory]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void AlignScribeReceiptRepairsTargetAndMismatchedSiblingInOneTransaction(
        string mismatchCode)
    {
        var materialized = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec() with
        {
            OtherAtomBinding = ("receipt-gap-sibling", "D5/S0/Carrier/Probe.probe"),
        });
        var inputs = DirectoryInputs(WithSiblingReceiptMismatch(materialized, mismatchCode));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.AlignScribeReceipt(
        [
            "--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid,
            "--atom-id", "receipt-gap-sibling", "--gid", inputs.Gid,
            "--base", "baseline",
        ]);

        Assert.True(result.Success, result.Error);
        Assert.True(inputs.VerifiedEmissions!.TryGet(
            inputs.Gid[..inputs.Gid.LastIndexOf('.')], out var verified));
        var after = BackfillInventoryLoader.LoadRoot(temporary.Path);
        foreach (var atomId in new[] { CoverWorld.DefaultAtomId, "receipt-gap-sibling" })
        {
            var entry = Assert.Single(
                after.RequireDigestionEntries(),
                item => item.AtomId == atomId);
            var receipt = Assert.Single(entry.Receipts.Scribe);
            Assert.Equal(verified.DefinitionSha256, receipt.DefinitionSha256);
            Assert.Equal(verified.EmissionSha256, receipt.EmissionSha256);
            Assert.Contains(
                $"atom_id={atomId} gid={inputs.Gid}",
                result.Output,
                StringComparison.Ordinal);
        }
    }

    [Fact]
    public void AlignScribeReceiptStillRejectsBatchWhenACoverageReceiptMismatchRemains()
    {
        var materialized = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec() with
        {
            OtherAtomBinding = ("receipt-gap-sibling", "D5/S0/Carrier/Probe.probe"),
        });
        var inputs = DirectoryInputs(
            WithSiblingReceiptMismatch(materialized, "coverage-receipt-mismatch"));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.AlignScribeReceipt(
        [
            "--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid,
            "--atom-id", "receipt-gap-sibling", "--gid", inputs.Gid,
            "--base", "baseline",
        ]);

        Assert.False(result.Success);
        Assert.Contains("coverage-receipt-mismatch", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    public static TheoryData<string[]> UnpairedOrDuplicatePairArguments => new()
    {
        new[] { "--atom-id", "a", "--gid", "g", "--atom-id", "b", "--base", "rev" },
        new[] { "--atom-id", "a", "--atom-id", "b", "--gid", "g", "--base", "rev" },
        new[] { "--gid", "g", "--atom-id", "a", "--base", "rev" },
        new[] { "--atom-id", "a", "--gid", "g", "--atom-id", "a", "--gid", "g", "--base", "rev" },
    };

    [Theory]
    [MemberData(nameof(UnpairedOrDuplicatePairArguments))]
    public void AlignScribeReceiptRejectsUnpairedOrDuplicatePairArguments(string[] arguments)
    {
        var materialized = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec());
        var inputs = DirectoryInputs(materialized);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.AlignScribeReceipt(arguments);

        Assert.False(result.Success);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }
}
