using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ShowAtomTests
{
    private const string SelfAtomId = "self-atom";
    private const string NoncanonicalSelfAtomId = "Noncanonical-self";
    private const string DirectParentId = "direct-parent";
    private const string ZeroSha256 =
        "sha256:0000000000000000000000000000000000000000000000000000000000000000";
    private const string OneSha256 =
        "sha256:1111111111111111111111111111111111111111111111111111111111111111";

    [Fact]
    public void ShowAtomIncludesBoundReceiptPointerForQueriedAtomAndReportsNoDirectParent()
    {
        var output = RunFormalizationPointers(SelfAtomId);

        Assert.Contains("FORMALIZATION_POINTERS\n", output, StringComparison.Ordinal);
        Assert.Contains(
            $"SELF_FORMALIZATION_POINTER status=available primary_gid={PrimaryGid(SelfAtomId)} "
                + $"receipt_path={ReceiptPath(SelfAtomId)}",
            output,
            StringComparison.Ordinal);
        Assert.DoesNotContain("current", output, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("PARENT_FORMALIZATIONS status=no-parent\n", output, StringComparison.Ordinal);
    }

    [Fact]
    public void ShowAtomSelfFormalizationStatusesAreMutuallyExclusive()
    {
        var available = RunFormalizationPointers(SelfAtomId);
        var withoutReceipt = RunFormalizationPointers(BoundaryAtomId);
        var unavailable = RunFormalizationPointers(
            SelfAtomId,
            receipts => receipts.Files[SelfAtomId] = RawRepositoryEntry.FromText(
                ReceiptPath(SelfAtomId),
                "{\n"));

        AssertSinglePointerStatus(
            available,
            "SELF_FORMALIZATION_POINTER ",
            "available",
            "self-without-receipt",
            "self-receipt-unavailable");
        AssertSinglePointerStatus(
            withoutReceipt,
            "SELF_FORMALIZATION_POINTER ",
            "self-without-receipt",
            "available",
            "self-receipt-unavailable");
        AssertSinglePointerStatus(
            unavailable,
            "SELF_FORMALIZATION_POINTER ",
            "self-receipt-unavailable",
            "available",
            "self-without-receipt");
    }

    [Fact]
    public void ShowAtomDistinguishesMissingSelfReceiptWithoutBlockingAuthoritativeText()
    {
        var output = RunFormalizationPointers(BoundaryAtomId);

        Assert.Contains(
            $"SELF_FORMALIZATION_POINTER status=self-without-receipt "
                + $"receipt_path={ReceiptPath(BoundaryAtomId)}",
            output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void ShowAtomTreatsMalformedJsonSelfReceiptAsUnavailableWithoutBlockingAuthoritativeText()
    {
        var output = RunFormalizationPointers(
            SelfAtomId,
            receipts => receipts.Files[SelfAtomId] = RawRepositoryEntry.FromText(
                ReceiptPath(SelfAtomId),
                "{"));

        AssertSelfReceiptUnavailable(output);
    }

    [Fact]
    public void ShowAtomTreatsNonObjectJsonSelfReceiptAsUnavailableWithoutBlockingAuthoritativeText()
    {
        var output = RunFormalizationPointers(
            SelfAtomId,
            receipts => receipts.Files[SelfAtomId] = RawRepositoryEntry.FromText(
                ReceiptPath(SelfAtomId),
                "[]\n"));

        AssertSelfReceiptUnavailable(output);
    }

    [Fact]
    public void ShowAtomTreatsClosedSchemaFailureSelfReceiptAsUnavailableWithoutBlockingAuthoritativeText()
    {
        var output = RunFormalizationPointers(
            SelfAtomId,
            receipts => receipts.Files[SelfAtomId] = RawRepositoryEntry.FromText(
                ReceiptPath(SelfAtomId),
                "{}\n"));

        AssertSelfReceiptUnavailable(output);
    }

    [Fact]
    public void ShowAtomTreatsAtomIdBindingMismatchAsUnavailableWithoutBlockingAuthoritativeText()
    {
        var output = RunFormalizationPointers(
            SelfAtomId,
            receipts => receipts.Files[SelfAtomId] = ReceiptFile(
                receipts.Entries[SelfAtomId],
                atomId: "different-atom"));

        AssertSelfReceiptUnavailable(output);
    }

    [Fact]
    public void ShowAtomTreatsCasBindingMismatchAsUnavailableWithoutBlockingAuthoritativeText()
    {
        var output = RunFormalizationPointers(
            SelfAtomId,
            receipts => receipts.Files[SelfAtomId] = ReceiptFile(
                receipts.Entries[SelfAtomId],
                casRef: ZeroSha256));

        AssertSelfReceiptUnavailable(output);
    }

    [Fact]
    public void ShowAtomTreatsRawSha256BindingMismatchAsUnavailableWithoutBlockingAuthoritativeText()
    {
        var output = RunFormalizationPointers(
            SelfAtomId,
            receipts => receipts.Files[SelfAtomId] = ReceiptFile(
                receipts.Entries[SelfAtomId],
                rawSha256: OneSha256));

        AssertSelfReceiptUnavailable(output);
    }

    [Fact]
    public void ShowAtomTreatsNoncanonicalSelfReceiptPathAsUnavailableWithoutBlockingAuthoritativeText()
    {
        var output = RunFormalizationPointers(NoncanonicalSelfAtomId);

        Assert.Contains(
            $"SELF_FORMALIZATION_POINTER status=self-receipt-unavailable "
                + $"receipt_path={ReceiptPath(NoncanonicalSelfAtomId)}",
            output,
            StringComparison.Ordinal);
        Assert.DoesNotContain(PrimaryGid(NoncanonicalSelfAtomId), output, StringComparison.Ordinal);
    }

    [Fact]
    public void ShowAtomIncludesBoundReceiptPointerForDirectChainParent()
    {
        var output = RunFormalizationPointers(BoundaryAtomId);

        Assert.Contains(
            $"PARENT_FORMALIZATION_POINTER parent_atom_id={DirectParentId} status=available "
                + $"primary_gid={PrimaryGid(DirectParentId)} receipt_path={ReceiptPath(DirectParentId)}",
            output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void ShowAtomParentFormalizationStatusesAreMutuallyExclusive()
    {
        var output = RunFormalizationPointers(BoundaryAtomId);

        AssertSinglePointerStatus(
            output,
            $"PARENT_FORMALIZATION_POINTER parent_atom_id={DirectParentId} ",
            "available",
            "parent-without-receipt",
            "parent-receipt-unavailable");
        AssertSinglePointerStatus(
            output,
            "PARENT_FORMALIZATION_POINTER parent_atom_id=missing-parent ",
            "parent-without-receipt",
            "available",
            "parent-receipt-unavailable");
        AssertSinglePointerStatus(
            output,
            "PARENT_FORMALIZATION_POINTER parent_atom_id=invalid-parent ",
            "parent-receipt-unavailable",
            "available",
            "parent-without-receipt");
    }

    [Fact]
    public void ShowAtomDoesNotPropagateGrandparentReceipt()
    {
        Assert.DoesNotContain(
            "PARENT_FORMALIZATION_POINTER parent_atom_id=grandparent ",
            RunFormalizationPointers(BoundaryAtomId),
            StringComparison.Ordinal);
    }

    [Fact]
    public void ShowAtomDoesNotIncludeUnrelatedReceiptContainer()
    {
        Assert.DoesNotContain(
            "PARENT_FORMALIZATION_POINTER parent_atom_id=unrelated-container ",
            RunFormalizationPointers(BoundaryAtomId),
            StringComparison.Ordinal);
    }

    [Fact]
    public void ShowAtomOrdersDirectParentsByAtomIdOrdinal()
    {
        var parentIds = RunFormalizationPointers(BoundaryAtomId)
            .Split('\n', StringSplitOptions.RemoveEmptyEntries)
            .Where(static line => line.StartsWith(
                "PARENT_FORMALIZATION_POINTER ",
                StringComparison.Ordinal))
            .Select(static line => line.Split(' ')[1]["parent_atom_id=".Length..]);

        Assert.Equal(
            ["a-parent", DirectParentId, "invalid-parent", "mismatch-parent", "missing-parent", "z-parent"],
            parentIds);
    }

    [Fact]
    public void ShowAtomDistinguishesMissingParentReceiptWithoutBlockingAuthoritativeText()
    {
        var output = RunFormalizationPointers(BoundaryAtomId);

        Assert.Contains(
            "PARENT_FORMALIZATION_POINTER parent_atom_id=missing-parent "
                + "status=parent-without-receipt",
            output,
            StringComparison.Ordinal);
        Assert.DoesNotContain("PARENT_FORMALIZATIONS status=no-parent", output, StringComparison.Ordinal);
    }

    [Fact]
    public void ShowAtomDistinguishesLoaderFailureAndBindingMismatchForParentReceipts()
    {
        var output = RunFormalizationPointers(BoundaryAtomId);

        Assert.Contains(
            "PARENT_FORMALIZATION_POINTER parent_atom_id=invalid-parent "
                + "status=parent-receipt-unavailable",
            output,
            StringComparison.Ordinal);
        Assert.Contains(
            "PARENT_FORMALIZATION_POINTER parent_atom_id=mismatch-parent "
                + "status=parent-receipt-unavailable",
            output,
            StringComparison.Ordinal);
        Assert.DoesNotContain(PrimaryGid("mismatch-parent"), output, StringComparison.Ordinal);
    }

    private static void AssertSelfReceiptUnavailable(string output)
    {
        Assert.Contains(
            $"SELF_FORMALIZATION_POINTER status=self-receipt-unavailable "
                + $"receipt_path={ReceiptPath(SelfAtomId)}",
            output,
            StringComparison.Ordinal);
        Assert.DoesNotContain(PrimaryGid(SelfAtomId), output, StringComparison.Ordinal);
    }

    private static void AssertSinglePointerStatus(
        string output,
        string linePrefix,
        string expectedStatus,
        params string[] excludedStatuses)
    {
        var line = Assert.Single(
            output.Split('\n'),
            candidate => candidate.StartsWith(linePrefix, StringComparison.Ordinal));
        Assert.Contains($"status={expectedStatus} ", line, StringComparison.Ordinal);
        foreach (var excludedStatus in excludedStatuses)
        {
            Assert.DoesNotContain($"status={excludedStatus} ", line, StringComparison.Ordinal);
        }
    }

    private static string RunFormalizationPointers(
        string atomId,
        Action<ReceiptFixture>? configure = null)
    {
        const string sourcePath = "fixtures/show-atom/formalization-pointers.md";
        const string rawText = "authoritative atom text\n";
        var fingerprints = DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(rawText));
        DigestionLedgerEntry WithChain(string id, string path, string[] chain) => Entry(
            "formalization-source",
            sourcePath,
            AtomizerRegistry.NoAtomizerId,
            id,
            path,
            fingerprints) with
        {
            Receipts = new DigestionReceipts([], [], [], [.. chain], null),
        };
        var entries = new[]
        {
            WithChain("z-parent", "theorem/z", [BoundaryAtomId]),
            WithChain("missing-parent", "theorem/missing", [BoundaryAtomId]),
            WithChain(DirectParentId, "theorem/direct", [BoundaryAtomId]),
            WithChain("unrelated-container", "theorem/unrelated", ["different-child"]),
            WithChain(BoundaryAtomId, "theorem/child", []),
            WithChain("mismatch-parent", "theorem/mismatch", [BoundaryAtomId]),
            WithChain("grandparent", "theorem/grandparent", [DirectParentId]),
            WithChain(SelfAtomId, "theorem/self", []),
            WithChain(NoncanonicalSelfAtomId, "theorem/noncanonical-self", []),
            WithChain("invalid-parent", "theorem/invalid", [BoundaryAtomId]),
            WithChain("a-parent", "theorem/a", [BoundaryAtomId]) with
            {
                ProjectedStatus = new(
                    DigestionMigrationState.Residual,
                    DigestionTruthState.Open),
            },
        };
        var byId = entries.ToDictionary(static entry => entry.AtomId, StringComparer.Ordinal);
        string[] receiptIds =
        [
            "a-parent",
            DirectParentId,
            "grandparent",
            "mismatch-parent",
            NoncanonicalSelfAtomId,
            SelfAtomId,
            "unrelated-container",
            "z-parent",
        ];
        var receiptFiles = receiptIds.ToDictionary(
            static id => id,
            id => ReceiptFile(byId[id]),
            StringComparer.Ordinal);
        receiptFiles["invalid-parent"] = RawRepositoryEntry.FromText(
            ReceiptPath("invalid-parent"),
            "{}\n");
        receiptFiles["mismatch-parent"] = ReceiptFile(
            byId["mismatch-parent"],
            casRef: ZeroSha256);
        var fixture = new ReceiptFixture(byId, receiptFiles);
        configure?.Invoke(fixture);
        var ledger = Document(
            "formalization-source",
            sourcePath,
            AtomizerRegistry.NoAtomizerId,
            [.. entries]);
        var snapshot = SnapshotWithLedger(
            ledger,
            [
                RawRepositoryEntry.FromText(sourcePath, rawText),
                RawRepositoryEntry.FromText(
                    DigestionCasStore.RootPath + fingerprints.RawSha256["sha256:".Length..],
                    rawText),
                .. fixture.Files.Values,
            ]);

        var result = Environment("/repo", snapshot).ShowAtom(["--atom-id", atomId]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(string.Empty, result.Error);
        Assert.Contains(
            $"BEGIN_RAW_TEXT\n{rawText}END_RAW_TEXT\n",
            result.Output,
            StringComparison.Ordinal);
        return result.Output;
    }

    private static RawRepositoryEntry ReceiptFile(
        DigestionLedgerEntry entry,
        string? atomId = null,
        string? casRef = null,
        string? rawSha256 = null) => new(
            ReceiptPath(entry.AtomId),
            DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
                atomId ?? entry.AtomId,
                PrimaryGid(entry.AtomId),
                new DigestionFormalizationSignature("Synthetic.receipt", "theorem", "True"),
                casRef ?? entry.CasRef,
                rawSha256 ?? entry.Fingerprints.RawSha256)));

    private static string PrimaryGid(string atomId) =>
        "D5/S0/Synthetic/Receipt."
        + atomId.Replace("-", "_", StringComparison.Ordinal);

    private static string ReceiptPath(string atomId) =>
        DigestionFormalizationReceipt.RootPath
        + atomId
        + DigestionFormalizationReceipt.PathSuffix;

    private sealed record ReceiptFixture(
        IReadOnlyDictionary<string, DigestionLedgerEntry> Entries,
        IDictionary<string, RawRepositoryEntry> Files);
}
