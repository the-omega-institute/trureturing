using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ShowAtomTests
{
    private static readonly string BoundaryAtomId = LabeledAtomId("boundary");
    private static readonly string SelfAtomId = LabeledAtomId("self");
    private static readonly string DirectParentId = LabeledAtomId("direct-parent");
    private static readonly string AParentId = LabeledAtomId("a-parent");
    private static readonly string GrandparentId = LabeledAtomId("grandparent");
    private static readonly string InvalidParentId = LabeledAtomId("invalid-parent");
    private static readonly string MismatchParentId = LabeledAtomId("mismatch-parent");
    private static readonly string MissingParentId = LabeledAtomId("missing-parent");
    private static readonly string UnrelatedContainerId = LabeledAtomId("unrelated-container");
    private static readonly string ZParentId = LabeledAtomId("z-parent");
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
                + $"gids={PrimaryGid(SelfAtomId)} "
                + $"receipt_path={ReceiptPath(SelfAtomId)}",
            output,
            StringComparison.Ordinal);
        Assert.DoesNotContain("current", output, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("PARENT_FORMALIZATIONS status=no-parent\n", output, StringComparison.Ordinal);
    }

    [Fact]
    public void ShowAtomIncludesEveryOrderedGidFromTheBoundReceipt()
    {
        var secondaryGid = SecondaryGid(SelfAtomId);
        var output = RunFormalizationPointers(
            SelfAtomId,
            receipts => receipts.Files[SelfAtomId] = ReceiptFile(
                receipts.Entries[SelfAtomId],
                hostedExtensions:
                [
                    new DigestionFormalizationExtension(
                        secondaryGid,
                        new DigestionFormalizationSignature("secondary", "theorem", "True")),
                ]));

        Assert.Contains(
            $"primary_gid={PrimaryGid(SelfAtomId)} "
                + $"gids={PrimaryGid(SelfAtomId)},{secondaryGid} ",
            output,
            StringComparison.Ordinal);
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
                atomId: LabeledAtomId("different-atom")));

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
    public void ShowAtomIncludesBoundReceiptPointerForDirectChainParent()
    {
        var output = RunFormalizationPointers(BoundaryAtomId);

        Assert.Contains(
            $"PARENT_FORMALIZATION_POINTER parent_atom_id={DirectParentId} status=available "
                + $"primary_gid={PrimaryGid(DirectParentId)} "
                + $"gids={PrimaryGid(DirectParentId)} "
                + $"receipt_path={ReceiptPath(DirectParentId)}",
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
            $"PARENT_FORMALIZATION_POINTER parent_atom_id={MissingParentId} ",
            "parent-without-receipt",
            "available",
            "parent-receipt-unavailable");
        AssertSinglePointerStatus(
            output,
            $"PARENT_FORMALIZATION_POINTER parent_atom_id={InvalidParentId} ",
            "parent-receipt-unavailable",
            "available",
            "parent-without-receipt");
    }

    [Fact]
    public void ShowAtomDoesNotPropagateGrandparentReceipt()
    {
        Assert.DoesNotContain(
            $"PARENT_FORMALIZATION_POINTER parent_atom_id={GrandparentId} ",
            RunFormalizationPointers(BoundaryAtomId),
            StringComparison.Ordinal);
    }

    [Fact]
    public void ShowAtomDoesNotIncludeUnrelatedReceiptContainer()
    {
        Assert.DoesNotContain(
            $"PARENT_FORMALIZATION_POINTER parent_atom_id={UnrelatedContainerId} ",
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
            new[]
            {
                AParentId,
                DirectParentId,
                InvalidParentId,
                MismatchParentId,
                MissingParentId,
                ZParentId,
            }.Order(StringComparer.Ordinal),
            parentIds);
    }

    [Fact]
    public void ShowAtomDistinguishesMissingParentReceiptWithoutBlockingAuthoritativeText()
    {
        var output = RunFormalizationPointers(BoundaryAtomId);

        Assert.Contains(
            $"PARENT_FORMALIZATION_POINTER parent_atom_id={MissingParentId} "
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
            $"PARENT_FORMALIZATION_POINTER parent_atom_id={InvalidParentId} "
                + "status=parent-receipt-unavailable",
            output,
            StringComparison.Ordinal);
        Assert.Contains(
            $"PARENT_FORMALIZATION_POINTER parent_atom_id={MismatchParentId} "
                + "status=parent-receipt-unavailable",
            output,
            StringComparison.Ordinal);
        Assert.DoesNotContain(PrimaryGid(MismatchParentId), output, StringComparison.Ordinal);
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
        var rawTextById = new Dictionary<string, string>(StringComparer.Ordinal);
        DigestionLedgerEntry WithChain(string label, string[] chain)
        {
            var rawText = LabeledAtomText(label);
            var fingerprints = DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(rawText));
            var id = BareAtomId(fingerprints.RawSha256);
            rawTextById.Add(id, rawText);
            return Entry(
                "formalization-source",
                sourcePath,
                AtomizerRegistry.NoAtomizerId,
                id,
                fingerprints) with
            {
                Receipts = new DigestionReceipts([], [], [], [.. chain], null),
            };
        }

        var entries = new[]
        {
            WithChain("z-parent", [BoundaryAtomId]),
            WithChain("missing-parent", [BoundaryAtomId]),
            WithChain("direct-parent", [BoundaryAtomId]),
            WithChain("unrelated-container", [LabeledAtomId("different-child")]),
            WithChain("boundary", []),
            WithChain("mismatch-parent", [BoundaryAtomId]),
            WithChain("grandparent", [DirectParentId]),
            WithChain("self", []),
            WithChain("invalid-parent", [BoundaryAtomId]),
            WithChain("a-parent", [BoundaryAtomId]) with
            {
                ProjectedStatus = new(
                    DigestionMigrationState.Residual,
                    DigestionTruthState.Open),
            },
        };
        var byId = entries.ToDictionary(static entry => entry.AtomId, StringComparer.Ordinal);
        string[] receiptIds =
        [
            AParentId,
            DirectParentId,
            GrandparentId,
            MismatchParentId,
            SelfAtomId,
            UnrelatedContainerId,
            ZParentId,
        ];
        var receiptFiles = receiptIds.ToDictionary(
            static id => id,
            id => ReceiptFile(byId[id]),
            StringComparer.Ordinal);
        receiptFiles[InvalidParentId] = RawRepositoryEntry.FromText(
            ReceiptPath(InvalidParentId),
            "{}\n");
        receiptFiles[MismatchParentId] = ReceiptFile(
            byId[MismatchParentId],
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
                RawRepositoryEntry.FromText(sourcePath, rawTextById[atomId]),
                .. rawTextById.Select(static item => RawRepositoryEntry.FromText(
                    DigestionCasStore.RootPath + item.Key,
                    item.Value)),
                .. fixture.Files.Values,
            ]);

        var result = Environment("/repo", snapshot).ShowAtom(["--atom-id", atomId]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(string.Empty, result.Error);
        Assert.Contains(
            $"BEGIN_RAW_TEXT\n{rawTextById[atomId]}END_RAW_TEXT\n",
            result.Output,
            StringComparison.Ordinal);
        return result.Output;
    }

    private static RawRepositoryEntry ReceiptFile(
        DigestionLedgerEntry entry,
        string? atomId = null,
        string? casRef = null,
        string? rawSha256 = null,
        ImmutableArray<DigestionFormalizationExtension> hostedExtensions = default) => new(
            ReceiptPath(entry.AtomId),
            DigestionFormalizationReceipt.Write(new DigestionFormalizationReceipt(
                atomId ?? entry.AtomId,
                PrimaryGid(entry.AtomId),
                new DigestionFormalizationSignature("Synthetic.receipt", "theorem", "True"),
                casRef ?? entry.CasRef,
                rawSha256 ?? entry.Fingerprints.RawSha256,
                hostedExtensions)));

    private static string PrimaryGid(string atomId) =>
        "D5/S0/Synthetic/Receipt.atom_" + atomId;

    private static string SecondaryGid(string atomId) =>
        "D5/S0/Synthetic/Receipt.secondary_" + atomId;

    private static string ReceiptPath(string atomId) =>
        DigestionFormalizationReceipt.RootPath
        + atomId
        + DigestionFormalizationReceipt.PathSuffix;

    private static string LabeledAtomId(string label) =>
        BareAtomId(DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(LabeledAtomText(label))).RawSha256);

    private static string LabeledAtomText(string label) =>
        $"authoritative atom text: {label}\n";

    private sealed record ReceiptFixture(
        IReadOnlyDictionary<string, DigestionLedgerEntry> Entries,
        IDictionary<string, RawRepositoryEntry> Files);
}
