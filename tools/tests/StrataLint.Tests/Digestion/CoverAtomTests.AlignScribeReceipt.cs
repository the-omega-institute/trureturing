using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CoverAtomTests
{
    [Fact]
    public void AlignScribeReceiptAcceptsDocumentGidAndRefreshesFingerprints()
    {
        var inputs = DocumentReceiptInputs();
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);

        var result = CoverWorld.Environment(temporary.Path, inputs, currentFiles)
            .AlignScribeReceipt(CoverWorld.AlignArgs(inputs));

        Assert.True(result.Success, result.Error);
        Assert.Contains($"gid={inputs.Gid}", result.Output, StringComparison.Ordinal);
        var entry = Assert.Single(
            BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries());
        var receipt = Assert.Single(entry.Receipts.Scribe);
        Assert.Equal(inputs.Gid, receipt.Gid);
        Assert.Equal(
            DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(
                currentFiles[ScribeEmissionAttestation.DefinitionPath(inputs.Gid)])).RawSha256,
            receipt.DefinitionSha256);
        Assert.Equal(
            DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(
                currentFiles[ScribeEmissionAttestation.EmissionPath(inputs.Gid)])).RawSha256,
            receipt.EmissionSha256);
        Assert.NotEqual("sha256:" + new string('a', 64), receipt.DefinitionSha256);
        Assert.NotEqual("sha256:" + new string('b', 64), receipt.EmissionSha256);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(2)]
    public void AlignScribeReceiptDocumentDomainStillRequiresExactlyOneReceipt(int receiptCount)
    {
        AssertDocumentAlignSucceeds();
        var inputs = DocumentReceiptInputs();
        var receipt = Assert.Single(Assert.Single(
            inputs.Document.RequireDigestionEntries()).Receipts.Scribe);
        var document = WithScribeReceipts(
            inputs.Document,
            CoverWorld.DefaultAtomId,
            Enumerable.Repeat(receipt, receiptCount).ToImmutableArray());
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        DirectoryLedgerTestSupport.ReplaceWithProjection(currentFiles, document);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);

        var result = CoverWorld.Environment(temporary.Path, inputs, currentFiles)
            .AlignScribeReceipt(CoverWorld.AlignArgs(inputs));

        Assert.False(result.Success);
        Assert.Contains("must have exactly one Scribe receipt", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    [Fact]
    public void AlignScribeReceiptRejectsInvalidGidWithoutWriting()
    {
        AssertDocumentAlignSucceeds();
        const string invalidGid = "not-a-gid";
        var inputs = DocumentReceiptInputs();
        var document = inputs.Document.WithDigestionSources(
            inputs.Document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries.Select(entry =>
                        entry.AtomId == CoverWorld.DefaultAtomId
                            ? entry with
                            {
                                Coverage = entry.Coverage
                                    .Select(edge => edge with { Gid = invalidGid })
                                    .ToImmutableArray(),
                                Receipts = entry.Receipts with
                                {
                                    Scribe = entry.Receipts.Scribe
                                        .Select(receipt => receipt with { Gid = invalidGid })
                                        .ToImmutableArray(),
                                },
                            }
                            : entry).ToImmutableArray(),
                })
                .ToImmutableArray());
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        DirectoryLedgerTestSupport.ReplaceWithProjection(currentFiles, document);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);

        var result = CoverWorld.Environment(temporary.Path, inputs, currentFiles).AlignScribeReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId, "--gid", invalidGid, "--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains(
            $"align GID must select a Lean declaration: {invalidGid}",
            result.Error,
            StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    [Fact]
    public void AlignScribeReceiptMixedDocumentAndDeclarationBatchIsAtomic()
    {
        var documentGid = CoverWorld.StaleReceiptSpec().ModuleGid;
        var inputs = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec() with
        {
            OtherAtomGid = documentGid,
            OtherMigration = "absorbed",
        });
        var arguments = new[]
        {
            "--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid,
            "--atom-id", CoverWorld.OtherAtomId, "--gid", documentGid,
            "--base", "baseline",
        };
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        using (var temporary = new TemporaryDirectory())
        {
            DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);

            var result = CoverWorld.Environment(temporary.Path, inputs, currentFiles)
                .AlignScribeReceipt(arguments);

            Assert.True(result.Success, result.Error);
            Assert.True(inputs.VerifiedEmissions!.TryGet(documentGid, out var verified));
            var after = BackfillInventoryLoader.LoadRoot(temporary.Path);
            foreach (var (atomId, gid) in new[]
                     {
                         (CoverWorld.DefaultAtomId, inputs.Gid),
                         (CoverWorld.OtherAtomId, documentGid),
                     })
            {
                var entry = Assert.Single(
                    after.RequireDigestionEntries(),
                    candidate => candidate.AtomId == atomId);
                var receipt = Assert.Single(entry.Receipts.Scribe);
                Assert.Equal(gid, receipt.Gid);
                Assert.Equal(verified.DefinitionSha256, receipt.DefinitionSha256);
                Assert.Equal(verified.EmissionSha256, receipt.EmissionSha256);
            }
        }

        var invalidDocument = WithScribeReceipts(
            inputs.Document,
            CoverWorld.OtherAtomId,
            []);
        var invalidFiles = new Dictionary<string, string>(currentFiles, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(invalidFiles, invalidDocument);
        using (var temporary = new TemporaryDirectory())
        {
            DirectoryLedgerTestSupport.Write(temporary.Path, invalidFiles);
            var before = DirectoryLedgerTestSupport.Image(temporary.Path);

            var result = CoverWorld.Environment(temporary.Path, inputs, invalidFiles)
                .AlignScribeReceipt(arguments);

            Assert.False(result.Success);
            Assert.Contains("must have exactly one Scribe receipt", result.Error, StringComparison.Ordinal);
            Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
        }
    }

    [Fact]
    public void AlignScribeReceiptUsesVerifiedFingerprintsAndIsIdempotent()
    {
        var inputs = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec());
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);

        var first = CoverWorld.Environment(temporary.Path, inputs, currentFiles)
            .AlignScribeReceipt(CoverWorld.AlignArgs(inputs));

        Assert.True(first.Success, first.Error);
        Assert.Contains("ALIGN_SCRIBE_RECEIPT", first.Output, StringComparison.Ordinal);
        Assert.Contains($"atom_id={CoverWorld.DefaultAtomId}", first.Output, StringComparison.Ordinal);
        Assert.Contains($"gid={inputs.Gid}", first.Output, StringComparison.Ordinal);
        Assert.Contains("old_definition_sha256=sha256:aaaaaaaa", first.Output, StringComparison.Ordinal);
        Assert.Contains("new_definition_sha256=sha256:", first.Output, StringComparison.Ordinal);
        Assert.Contains("old_emission_sha256=sha256:bbbbbbbb", first.Output, StringComparison.Ordinal);
        Assert.Contains("new_emission_sha256=sha256:", first.Output, StringComparison.Ordinal);
        Assert.Contains("ledger_changed=true", first.Output, StringComparison.Ordinal);
        var afterFirst = DirectoryLedgerTestSupport.Image(
            BackfillInventoryLoader.LoadRoot(temporary.Path));
        Assert.True(inputs.VerifiedEmissions!.TryGet(
            inputs.Gid[..inputs.Gid.LastIndexOf('.')], out var verifiedRecord));
        Assert.Equal(
            ExpectedAlignedScribeImage(inputs, verifiedRecord),
            afterFirst);

        var replayFiles = new Dictionary<string, string>(currentFiles, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(
            replayFiles,
            BackfillInventoryLoader.LoadRoot(temporary.Path));
        var second = CoverWorld.Environment(temporary.Path, inputs, replayFiles)
            .AlignScribeReceipt(CoverWorld.AlignArgs(inputs));

        Assert.True(second.Success, second.Error);
        Assert.Contains("ledger_changed=false", second.Output, StringComparison.Ordinal);
        Assert.Equal(
            afterFirst,
            DirectoryLedgerTestSupport.Image(BackfillInventoryLoader.LoadRoot(temporary.Path)));
    }

    public static TheoryData<string, string> UnknownAlignTargets => new()
    {
        { "no-such-atom", "D5/S0/Carrier/Probe.probe" },
        { CoverWorld.DefaultAtomId, "D5/S0/Carrier/Probe.missing" },
    };

    [Theory]
    [MemberData(nameof(UnknownAlignTargets))]
    public void AlignScribeReceiptFailsClosedForUnknownAtomOrGid(string atomId, string gid)
    {
        var inputs = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec());
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, inputs.Ledger, new UTF8Encoding(false));

        var result = CoverWorld.Environment(temporary.Path, inputs, inputs.Files).AlignScribeReceipt(
            ["--atom-id", atomId, "--gid", gid]);

        Assert.False(result.Success);
        Assert.Contains("ALIGN_SCRIBE_RECEIPT_INVALID", result.Error, StringComparison.Ordinal);
        Assert.Equal(inputs.Ledger, File.ReadAllText(outputPath));
    }

    [Fact]
    public void AlignScribeReceiptRejectsSiblingStatusDriftBeforeWritingLedger()
    {
        var spec = CoverWorld.StaleReceiptSpec() with
        {
            OtherAtomGid = "D5/S0/Carrier/Probe.sibling",
        };
        var inputs = CoverWorld.Materialize(spec);
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);
        var before = DirectoryLedgerTestSupport.Image(BackfillInventoryLoader.LoadRoot(temporary.Path));
        var result = CoverWorld.Environment(temporary.Path, inputs, currentFiles)
            .AlignScribeReceipt(CoverWorld.AlignArgs(inputs));
        Assert.False(result.Success);
        Assert.Contains("digest status is invalid", result.Error, StringComparison.Ordinal);
        Assert.Contains(CoverWorld.OtherAtomId, result.Error, StringComparison.Ordinal);
        Assert.Equal(before,
            DirectoryLedgerTestSupport.Image(BackfillInventoryLoader.LoadRoot(temporary.Path)));
    }

    private static CoverInputs DocumentReceiptInputs() =>
        CoverWorld.Materialize(CoverWorld.StaleReceiptSpec() with
        {
            Declaration = null,
            InitialCoverage = [CoverWorld.StaleReceiptSpec().ModuleGid],
        });

    private static void AssertDocumentAlignSucceeds()
    {
        var inputs = DocumentReceiptInputs();
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);

        var result = CoverWorld.Environment(temporary.Path, inputs, currentFiles)
            .AlignScribeReceipt(CoverWorld.AlignArgs(inputs));

        Assert.True(result.Success, result.Error);
    }

    private static BackfillInventoryDocument WithScribeReceipts(
        BackfillInventoryDocument document,
        string atomId,
        ImmutableArray<DigestionScribeReceipt> receipts) =>
        document.WithDigestionSources(
            document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries.Select(entry => entry.AtomId == atomId
                        ? entry with
                        {
                            Receipts = entry.Receipts with { Scribe = receipts },
                        }
                        : entry).ToImmutableArray(),
                })
                .ToImmutableArray());
}
