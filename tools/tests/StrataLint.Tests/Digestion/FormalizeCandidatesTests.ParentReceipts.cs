using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class FormalizeCandidatesTests
{
    [Fact]
    public void FormalizeCandidatesIncludesDirectParentReceiptForChainChild()
    {
        var child = Entry("source", "chain-child", "定理", "2.3");
        var parent = Entry(
            "source",
            "chain-parent",
            "定理",
            "2.4",
            chainAtoms: [child.AtomId]);
        var receiptPath = DigestionFormalizationReceipt.RootPath
            + parent.AtomId
            + DigestionFormalizationReceipt.PathSuffix;

        var result = Run(
            [parent, child],
            formalizationReceipts: new Dictionary<string, byte[]>
            {
                [parent.AtomId] = ValidReceipt(parent),
            });

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        Assert.Equal(
            "stratalint-formalize-candidates-v4",
            json.RootElement.GetProperty("schema").GetString());
        var candidate = Assert.Single(
            json.RootElement.GetProperty("candidates").EnumerateArray(),
            item => item.GetProperty("atom_id").GetString() == child.AtomId);
        var parentReceipt = Assert.Single(
            candidate.GetProperty("parent_receipts").EnumerateArray());
        Assert.Equal(parent.AtomId, parentReceipt.GetProperty("parent_atom_id").GetString());
        Assert.Equal(
            "D5/S0/Synthetic/Receipt.chain_parent",
            parentReceipt.GetProperty("primary_gid").GetString());
        Assert.Equal(receiptPath, parentReceipt.GetProperty("receipt_path").GetString());
    }

    [Fact]
    public void FormalizeCandidatesDoesNotAttachReceiptFromUnrelatedContainer()
    {
        var child = Entry("source", "chain-child-filtered", "定理", "2.5");
        var parent = Entry(
            "source",
            "chain-parent-filtered",
            "定理",
            "2.6",
            chainAtoms: [child.AtomId]);
        var unrelated = Entry(
            "source",
            "unrelated-container",
            "定理",
            "2.7",
            chainAtoms: ["different-child"]);

        var result = Run(
            [parent, unrelated, child],
            formalizationReceipts: new Dictionary<string, byte[]>
            {
                [parent.AtomId] = ValidReceipt(parent),
                [unrelated.AtomId] = ValidReceipt(unrelated),
            });

        Assert.True(result.Success, result.Error);
        using var json = JsonDocument.Parse(result.Output);
        var candidate = Assert.Single(
            json.RootElement.GetProperty("candidates").EnumerateArray(),
            item => item.GetProperty("atom_id").GetString() == child.AtomId);
        var parentAtomIds = candidate.GetProperty("parent_receipts")
            .EnumerateArray()
            .Select(static receipt => receipt.GetProperty("parent_atom_id").GetString())
            .ToArray();
        Assert.Contains(parent.AtomId, parentAtomIds);
        Assert.DoesNotContain(unrelated.AtomId, parentAtomIds);
    }
}
