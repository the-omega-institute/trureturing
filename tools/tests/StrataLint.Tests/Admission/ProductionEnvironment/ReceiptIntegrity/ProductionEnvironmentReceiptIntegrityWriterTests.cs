using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Theory]
    [InlineData("coverage-receipt-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void CoverBlocksNewReceiptIntegrityIdentityBeforeWritingAnyLedgerByte(string mismatchCode)
    {
        var inputs = ReceiptIntegrityInputs(CoverSpecForReceiptWriter(), mismatchCode, includeInBaseline: false);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);

        var result = ReceiptIntegrityEnvironment(temporary.Path, inputs)
            .CoverAtom(CoverArgs(inputs));

        Assert.False(result.Success);
        Assert.Contains(mismatchCode, result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    [Theory]
    [InlineData("coverage-receipt-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void IngestBlocksNewReceiptIntegrityIdentityBeforeWritingAnyLedgerByte(string mismatchCode)
    {
        var inputs = ReceiptIntegrityInputs(CoverSpecForReceiptWriter(), mismatchCode, includeInBaseline: false);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);

        var result = ReceiptIntegrityEnvironment(temporary.Path, inputs)
            .Ingest(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains(mismatchCode, result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    [Theory]
    [InlineData("coverage-receipt-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void AlignScribeBlocksNewSiblingReceiptIntegrityIdentityBeforeWritingAnyLedgerByte(
        string mismatchCode)
    {
        var inputs = ReceiptIntegrityInputs(
            CoverSpecForReceiptWriter(staleTargetReceipt: true),
            mismatchCode,
            includeInBaseline: false);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);

        var result = ReceiptIntegrityEnvironment(temporary.Path, inputs).AlignScribeReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid, "--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains(mismatchCode, result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    [Theory]
    [InlineData("coverage-receipt-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void CoverObservesUnchangedBaselineReceiptIntegrityIdentity(string mismatchCode)
    {
        var inputs = ReceiptIntegrityInputs(CoverSpecForReceiptWriter(), mismatchCode, includeInBaseline: true);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);

        var result = ReceiptIntegrityEnvironment(temporary.Path, inputs)
            .CoverAtom(CoverArgs(inputs));

        Assert.True(result.Success, result.Error);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("coverage-receipt-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void IngestObservesUnchangedBaselineReceiptIntegrityIdentity(string mismatchCode)
    {
        var inputs = ReceiptIntegrityInputs(CoverSpecForReceiptWriter(), mismatchCode, includeInBaseline: true);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);

        var result = ReceiptIntegrityEnvironment(temporary.Path, inputs)
            .Ingest(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
    }

    [Theory]
    [InlineData("coverage-receipt-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void AlignScribeObservesUnchangedSiblingIdentityWhileShrinkingItsExactTarget(
        string mismatchCode)
    {
        var inputs = ReceiptIntegrityInputs(
            CoverSpecForReceiptWriter(staleTargetReceipt: true),
            mismatchCode,
            includeInBaseline: true);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);

        var result = ReceiptIntegrityEnvironment(temporary.Path, inputs).AlignScribeReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid, "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("coverage-receipt-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void CoverAllowsTouchedBaselineReceiptIntegrityIdentityWhenIdentityIsUnchanged(
        string mismatchCode)
    {
        var inputs = ReceiptIntegrityInputs(
            CoverSpecForReceiptWriter(),
            mismatchCode,
            includeInBaseline: true,
            touchExistingBadAtom: true);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);

        var result = ReceiptIntegrityEnvironment(temporary.Path, inputs)
            .CoverAtom(CoverArgs(inputs));

        Assert.True(result.Success, result.Error);
    }

    [Theory]
    [InlineData("coverage-receipt-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void IngestAllowsTouchedBaselineReceiptIntegrityIdentityWhenIdentityIsUnchanged(
        string mismatchCode)
    {
        var inputs = ReceiptIntegrityInputs(
            CoverSpecForReceiptWriter(),
            mismatchCode,
            includeInBaseline: true,
            touchExistingBadAtom: true);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);

        var result = ReceiptIntegrityEnvironment(temporary.Path, inputs)
            .Ingest(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
    }

    [Theory]
    [InlineData("coverage-receipt-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void AlignScribeAllowsTouchedBaselineReceiptIntegrityIdentityWhenIdentityIsUnchanged(
        string mismatchCode)
    {
        var inputs = ReceiptIntegrityInputs(
            CoverSpecForReceiptWriter(staleTargetReceipt: true),
            mismatchCode,
            includeInBaseline: true,
            touchExistingBadAtom: true);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);

        var result = ReceiptIntegrityEnvironment(temporary.Path, inputs).AlignScribeReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid, "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
    }

    [Fact]
    public void CoverDoesNotTreatLegalMissingReceiptGapsAsFatal()
    {
        var inputs = InputsWithUnreceiptedSibling(CoverSpecForReceiptWriter());
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);

        var result = ReceiptIntegrityEnvironment(temporary.Path, inputs)
            .CoverAtom(CoverArgs(inputs));

        Assert.True(result.Success, result.Error);
    }

    [Fact]
    public void IngestDoesNotTreatLegalMissingReceiptGapsAsFatal()
    {
        var inputs = InputsWithUnreceiptedSibling(CoverSpecForReceiptWriter());
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);

        var result = ReceiptIntegrityEnvironment(temporary.Path, inputs)
            .Ingest(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
    }

    [Fact]
    public void AlignScribeDoesNotTreatLegalMissingSiblingReceiptGapsAsFatal()
    {
        var inputs = InputsWithUnreceiptedSibling(CoverSpecForReceiptWriter(staleTargetReceipt: true));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);

        var result = ReceiptIntegrityEnvironment(temporary.Path, inputs).AlignScribeReceipt(
            ["--atom-id", CoverWorld.DefaultAtomId, "--gid", inputs.Gid, "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
    }

    private static CoverSpec CoverSpecForReceiptWriter(bool staleTargetReceipt = false)
    {
        var spec = staleTargetReceipt
            ? CoverWorld.StaleReceiptSpec() with { BaselineTargetIdentical = true }
            : new CoverSpec();
        return spec with
        {
            SecondaryTarget = ("D5/S0/Carrier/ReceiptSibling", "sibling"),
            OtherAtomBinding = ("receipt-integrity-sibling", "D5/S0/Carrier/ReceiptSibling.sibling"),
        };
    }

    private static CoverInputs InputsWithUnreceiptedSibling(CoverSpec spec) =>
        DirectoryInputs(CoverWorld.Materialize(spec));

    private static CoverInputs ReceiptIntegrityInputs(
        CoverSpec spec,
        string mismatchCode,
        bool includeInBaseline,
        bool touchExistingBadAtom = false)
    {
        var inputs = DirectoryInputs(CoverWorld.Materialize(spec));
        var baselineMismatchDocument = WithReceiptIntegrityMismatch(inputs, inputs.Document, mismatchCode);
        var candidateDocument = touchExistingBadAtom
            ? TouchExistingBadAtom(baselineMismatchDocument)
            : baselineMismatchDocument;
        var currentFiles = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(currentFiles, candidateDocument);
        var baselineFiles = new Dictionary<string, string>(inputs.Baseline, StringComparer.Ordinal);
        if (includeInBaseline)
        {
            var baselineDocument = LoadReceiptIntegrityDocument(baselineFiles);
            var sibling = baselineMismatchDocument.RequireDigestionEntries().Single(static entry =>
                entry.AtomId == "receipt-integrity-sibling");
            baselineDocument = baselineDocument.WithDigestionSources(
                baselineDocument.RequireDigestionSources()
                    .Select(source => source.SourceId == sibling.SourceId
                        ? source with { Entries = source.Entries.Add(sibling) }
                        : source)
                    .ToImmutableArray());
            DirectoryLedgerTestSupport.ReplaceWithProjection(baselineFiles, baselineDocument);
        }

        return inputs with
        {
            Files = currentFiles,
            Baseline = baselineFiles,
            Document = candidateDocument,
        };
    }

    private static BackfillInventoryDocument TouchExistingBadAtom(
        BackfillInventoryDocument document)
    {
        var normalized = "sha256:" + new string('d', 64);
        return document.WithDigestionSources(
            document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries.Select(entry => entry.AtomId == "receipt-integrity-sibling"
                        ? entry with
                        {
                            Fingerprints = entry.Fingerprints with
                            {
                                NormalizedSha256 = normalized,
                            },
                        }
                        : entry).ToImmutableArray(),
                })
                .ToImmutableArray());
    }

    private static BackfillInventoryDocument WithReceiptIntegrityMismatch(
        CoverInputs inputs,
        BackfillInventoryDocument document,
        string mismatchCode)
    {
        const string siblingAtomId = "receipt-integrity-sibling";
        const string gid = "D5/S0/Carrier/ReceiptSibling.sibling";
        const string documentGid = "D5/S0/Carrier/ReceiptSibling";
        Assert.True(inputs.VerifiedEmissions!.TryGet(documentGid, out var verified));
        var targetSha256 = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(inputs.Files[documentGid + ".lean"])).RawSha256;
        var mismatchSha256 = "sha256:" + new string('c', 64);
        return document.WithDigestionSources(
            document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries.Select(entry => entry.AtomId == siblingAtomId
                        ? entry with
                        {
                            Receipts = entry.Receipts with
                            {
                                Coverage =
                                [
                                    new DigestionCoverageReceipt(
                                        gid,
                                        entry.Fingerprints.RawSha256,
                                        mismatchCode == "coverage-receipt-mismatch"
                                            ? mismatchSha256
                                            : targetSha256),
                                ],
                                Scribe =
                                [
                                    new DigestionScribeReceipt(
                                        gid,
                                        mismatchCode == "scribe-definition-mismatch"
                                            ? mismatchSha256
                                            : verified.DefinitionSha256,
                                        mismatchCode == "scribe-emission-mismatch"
                                            ? mismatchSha256
                                            : verified.EmissionSha256),
                                ],
                            },
                        }
                        : entry).ToImmutableArray(),
                })
                .ToImmutableArray());
    }

    private static ProductionCliEnvironment ReceiptIntegrityEnvironment(
        string repositoryRoot,
        CoverInputs inputs) =>
        new(
            repositoryRoot,
            new FakeRepositoryGateway(
                ReceiptIntegrityChanges(inputs.Baseline, inputs.Files),
                CoverWorld.Raw(inputs.Files),
                CoverWorld.Raw(inputs.Baseline)),
            new FakeLeanReportSource(inputs.Report),
            new FakeScribeEmissionVerifier(inputs.VerifiedEmissions));

    private static RawChangeSet ReceiptIntegrityChanges(
        IReadOnlyDictionary<string, string> baseline,
        IReadOnlyDictionary<string, string> candidate) =>
        RawChangeSet.Create(baseline.Keys
            .Union(candidate.Keys, StringComparer.Ordinal)
            .Where(path => !baseline.TryGetValue(path, out var baselineText)
                || !candidate.TryGetValue(path, out var candidateText)
                || !string.Equals(baselineText, candidateText, StringComparison.Ordinal)));

    private static BackfillInventoryDocument LoadReceiptIntegrityDocument(
        IReadOnlyDictionary<string, string> files)
    {
        var raw = CoverWorld.Raw(files);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        return BackfillInventoryLoader.Load(snapshot);
    }
}
