using System.Text; using StrataLint.Engine;
namespace StrataLint.Tests; public sealed partial class ShowAtomTests
{
    private const string SelfAtomId = "self-atom", DirectParentId = "direct-parent";
    [Fact] public void ShowAtomIncludesCurrentReceiptForQueriedAtomAndReportsNoDirectParent()
    {
        var output = RunFormalizationPointers(SelfAtomId); Assert.Contains($"SELF_FORMALIZATION status=available primary_gid={PrimaryGid(SelfAtomId)} receipt_path={ReceiptPath(SelfAtomId)}", output);
        Assert.Contains("PARENT_FORMALIZATIONS status=no-parent\n", output);
    }
    [Fact] public void ShowAtomIncludesCurrentReceiptForDirectChainParent() => Assert.Contains(
        $"parent_atom_id={DirectParentId} status=available primary_gid={PrimaryGid(DirectParentId)} receipt_path={ReceiptPath(DirectParentId)}", RunFormalizationPointers(BoundaryAtomId));
    [Fact] public void ShowAtomDoesNotPropagateGrandparentReceipt() => Assert.DoesNotContain(
        "PARENT_FORMALIZATION parent_atom_id=grandparent ", RunFormalizationPointers(BoundaryAtomId));
    [Fact] public void ShowAtomDoesNotIncludeUnrelatedReceiptContainer() => Assert.DoesNotContain(
        "PARENT_FORMALIZATION parent_atom_id=unrelated-container ", RunFormalizationPointers(BoundaryAtomId));
    [Fact] public void ShowAtomOrdersDirectParentsByAtomIdOrdinal() => Assert.Equal(
        ["a-parent", DirectParentId, "invalid-parent", "mismatch-parent", "missing-parent", "z-parent"],
        RunFormalizationPointers(BoundaryAtomId).Split('\n', StringSplitOptions.RemoveEmptyEntries)
            .Where(static line => line.StartsWith("PARENT_FORMALIZATION ", StringComparison.Ordinal))
            .Select(static line => line.Split(' ')[1]["parent_atom_id=".Length..]));
    [Fact] public void ShowAtomDistinguishesMissingParentReceiptWithoutBlockingAuthoritativeText()
    {
        var output = RunFormalizationPointers(BoundaryAtomId); Assert.Contains("parent_atom_id=missing-parent status=parent-without-receipt", output);
        Assert.DoesNotContain("PARENT_FORMALIZATIONS status=no-parent", output);
    }
    [Fact] public void ShowAtomDistinguishesLoaderFailureAndBindingMismatchWithoutBlockingAuthoritativeText()
    {
        var output = RunFormalizationPointers(BoundaryAtomId);
        Assert.Contains("parent_atom_id=invalid-parent status=parent-receipt-unavailable", output); Assert.Contains(
            "parent_atom_id=mismatch-parent status=parent-receipt-unavailable", output);
        Assert.DoesNotContain(PrimaryGid("mismatch-parent"), output);
    }
    private static string RunFormalizationPointers(string atomId)
    {
        const string sourcePath = "fixtures/show-atom/formalization-pointers.md";
        const string rawText = "authoritative atom text\n";
        var fingerprints = DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(rawText));
        DigestionLedgerEntry WithChain(string id, string path, string[] chain) => Entry("formalization-source",
            sourcePath, AtomizerRegistry.NoAtomizerId, id, path, fingerprints) with
            { Receipts = new DigestionReceipts([], [], [], [.. chain], null) };
        var entries = new[] {
            WithChain("a-parent", "theorem/a", [BoundaryAtomId]) with { ProjectedStatus = new(DigestionMigrationState.Residual, DigestionTruthState.Open) },
            WithChain(BoundaryAtomId, "theorem/child", []),
            WithChain(DirectParentId, "theorem/direct", [BoundaryAtomId]),
            WithChain("grandparent", "theorem/grandparent", [DirectParentId]),
            WithChain("invalid-parent", "theorem/invalid", [BoundaryAtomId]),
            WithChain("mismatch-parent", "theorem/mismatch", [BoundaryAtomId]),
            WithChain("missing-parent", "theorem/missing", [BoundaryAtomId]),
            WithChain(SelfAtomId, "theorem/self", []),
            WithChain("unrelated-container", "theorem/unrelated", ["different-child"]),
            WithChain("z-parent", "theorem/z", [BoundaryAtomId]) };
        var byId = entries.ToDictionary(static entry => entry.AtomId, StringComparer.Ordinal);
        string[] receiptIds = ["a-parent", DirectParentId, "grandparent", "mismatch-parent", SelfAtomId, "unrelated-container", "z-parent"];
        var receipts = receiptIds.Select(id => ReceiptFile(byId[id])).Append(
            RawRepositoryEntry.FromText(ReceiptPath("invalid-parent"), "{}\n")).ToArray();
        receipts[3] = ReceiptFile(byId["mismatch-parent"], "sha256:0000000000000000000000000000000000000000000000000000000000000000");
        var ledger = Document("formalization-source", sourcePath, AtomizerRegistry.NoAtomizerId, [.. entries]);
        var snapshot = SnapshotWithLedger(ledger, [RawRepositoryEntry.FromText(sourcePath, rawText), RawRepositoryEntry.FromText(
            DigestionCasStore.RootPath + fingerprints.RawSha256["sha256:".Length..], rawText), .. receipts]);
        var result = Environment("/repo", snapshot).ShowAtom(["--atom-id", atomId]);
        Assert.True(result.Success, result.Error); Assert.Equal(string.Empty, result.Error);
        Assert.Contains($"BEGIN_RAW_TEXT\n{rawText}END_RAW_TEXT\n", result.Output);
        return result.Output;
    }
    private static RawRepositoryEntry ReceiptFile(DigestionLedgerEntry entry, string? casRef = null) => new(
        ReceiptPath(entry.AtomId), DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
            entry.AtomId, PrimaryGid(entry.AtomId), new("Synthetic.receipt", "theorem", "True"),
            casRef ?? entry.CasRef, entry.Fingerprints.RawSha256)));
    private static string PrimaryGid(string atomId) => "D5/S0/Synthetic/Receipt." + atomId.Replace("-", "_", StringComparison.Ordinal);
    private static string ReceiptPath(string atomId) => DigestionFormalizationReceipt.RootPath + atomId + DigestionFormalizationReceipt.PathSuffix;
}
