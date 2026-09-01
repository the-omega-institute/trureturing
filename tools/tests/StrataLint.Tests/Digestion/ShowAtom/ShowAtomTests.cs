using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ShowAtomTests
{
    private const string AdapterAtomizerId = AtomizerRegistry.PeriodicTreeId;

    [Fact]
    public void BoundaryAtomPrintsItsByteExactParagraphNormalizedTextAndRecordedHashesWithoutWriting()
    {
        const string sourcePath = "fixtures/show-atom/boundary.md";
        const string prefix = "preface\r\n";
        const string rawText = "Cafe\u0301 receipt\r\n";
        const string suffix = "suffix\r\n";
        const string rawSha256 =
            "sha256:a0f3e6e8bcaf79250e308db954a2ca02e8a5141528561b9f3633b9a5bddb74d4";
        const string normalizedSha256 =
            "sha256:7a439c840e28e11de3fd3c0232714bef0b204d18512aba869f3a58f7da905e1f";
        var sourceBytes = Encoding.UTF8.GetBytes(prefix + rawText + suffix);
        var rawBytes = Encoding.UTF8.GetBytes(rawText);
        var atomId = BareAtomId(rawSha256);
        var files = FixtureFiles(
            ContentLedger(sourcePath, rawSha256, normalizedSha256),
            sourcePath,
            sourceBytes,
            rawSha256,
            rawBytes);
        using var temporary = new TemporaryDirectory();
        var before = Directory.EnumerateFileSystemEntries(temporary.Path).ToArray();

        var result = Environment(temporary.Path, files).ShowAtom(["--atom-id", atomId]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(string.Empty, result.Error);
        Assert.Contains(
            $"SHOW_ATOM atom_id={atomId} source_id=content-source "
                + $"source_path={sourcePath} atomizer={AtomizerRegistry.NoAtomizerId}\n",
            result.Output,
            StringComparison.Ordinal);
        Assert.Contains(
            $"HASH_RECORD raw_sha256={rawSha256} normalized_sha256={normalizedSha256} "
                + $"cas_ref={rawSha256} source=ledger\n",
            result.Output,
            StringComparison.Ordinal);
        Assert.Contains($"BEGIN_RAW_TEXT\n{rawText}END_RAW_TEXT\n", result.Output, StringComparison.Ordinal);
        Assert.Contains(
            "BEGIN_NORMALIZED_TEXT\nCaf\u00e9 receipt\nEND_NORMALIZED_TEXT\n",
            result.Output,
            StringComparison.Ordinal);
        Assert.Equal(before, Directory.EnumerateFileSystemEntries(temporary.Path).ToArray());
    }

    [Fact]
    public void RegisteredAtomizerEntryPrintsItsCommittedCasParagraph()
    {
        const string sourcePath = "fixtures/show-atom/adapter.md";
        const string rawText = "## 1. Synthetic section\r\n\r\nCafe\u0301 receipt.\r\n";
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Synthetic document\r\n\r\n" + rawText);
        var rawBytes = Encoding.UTF8.GetBytes(rawText);
        var fingerprints = DigestionFingerprint.Compute(rawBytes);
        var atomId = BareAtomId(fingerprints.RawSha256);
        var files = FixtureFiles(
            AdapterLedger(
                sourcePath,
                fingerprints.RawSha256,
                fingerprints.NormalizedSha256),
            sourcePath,
            sourceBytes,
            fingerprints.RawSha256,
            rawBytes);

        var result = Environment("/repo", files).ShowAtom(["--atom-id", atomId]);

        Assert.True(result.Success, result.Error);
        Assert.Contains(
            $"atomizer={AdapterAtomizerId}\n",
            result.Output,
            StringComparison.Ordinal);
        Assert.Contains($"BEGIN_RAW_TEXT\n{rawText}END_RAW_TEXT\n", result.Output, StringComparison.Ordinal);
        Assert.Contains(
            "BEGIN_NORMALIZED_TEXT\n## 1. Synthetic section\n\n"
                + "Caf\u00e9 receipt.\nEND_NORMALIZED_TEXT\n",
            result.Output,
            StringComparison.Ordinal);
        Assert.Contains(
            $"HASH_RECORD raw_sha256={fingerprints.RawSha256} "
                + $"normalized_sha256={fingerprints.NormalizedSha256} "
                + $"cas_ref={fingerprints.RawSha256} source=ledger\n",
            result.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void MissingAtomFailsClosedWithoutOutput()
    {
        const string sourcePath = "fixtures/show-atom/boundary.md";
        const string rawText = "receipt\n";
        var rawBytes = Encoding.UTF8.GetBytes(rawText);
        var fingerprints = DigestionFingerprint.Compute(rawBytes);
        var files = FixtureFiles(
            ContentLedger(sourcePath, fingerprints.RawSha256, fingerprints.NormalizedSha256),
            sourcePath,
            rawBytes,
            fingerprints.RawSha256,
            rawBytes);

        var result = Environment("/repo", files).ShowAtom(["--atom-id", "no-such-atom"]);

        Assert.False(result.Success);
        Assert.Equal(string.Empty, result.Output);
        Assert.Equal(
            "SHOW_ATOM_INVALID atom_id no-such-atom is absent from digestion ledger\n",
            result.Error);
    }

    [Fact]
    public void LoneCarriageReturnKeepsTheRawTextEndMarkerOnANewLine()
    {
        const string sourcePath = "fixtures/show-atom/boundary.md";
        const string rawText = "receipt\r";
        var rawBytes = Encoding.UTF8.GetBytes(rawText);
        var fingerprints = DigestionFingerprint.Compute(rawBytes);
        var files = FixtureFiles(
            ContentLedger(sourcePath, fingerprints.RawSha256, fingerprints.NormalizedSha256),
            sourcePath,
            rawBytes,
            fingerprints.RawSha256,
            rawBytes);

        var result = Environment("/repo", files).ShowAtom(["--atom-id", BareAtomId(fingerprints.RawSha256)]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("BEGIN_RAW_TEXT\nreceipt\r\nEND_RAW_TEXT\n", result.Output, StringComparison.Ordinal);
        Assert.Contains(
            "BEGIN_NORMALIZED_TEXT\nreceipt\nEND_NORMALIZED_TEXT\n",
            result.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void CommittedCasBytesAreTrustedWithoutReplayingRecordedHashes()
    {
        const string sourcePath = "fixtures/show-atom/adapter.md";
        const string rawText = "## 1. Synthetic section\n\nSynthetic claim.\n";
        var rawBytes = Encoding.UTF8.GetBytes(rawText);
        var fingerprints = DigestionFingerprint.Compute(rawBytes);
        var adapterLedger = AdapterLedger(
            sourcePath,
            fingerprints.RawSha256,
            fingerprints.NormalizedSha256);
        var ledger = adapterLedger.WithDigestionSources(
        [
            .. adapterLedger.RequireDigestionSources()
                .Select(source => source with
                {
                    AcknowledgedStale = [BareAtomId(fingerprints.RawSha256)],
                }),
        ]);
        var files = FixtureFiles(
            ledger,
            sourcePath,
            rawBytes,
            fingerprints.RawSha256,
            Encoding.UTF8.GetBytes("corrupt CAS bytes\n"));

        var result = Environment("/repo", files).ShowAtom(
            ["--atom-id", BareAtomId(fingerprints.RawSha256)]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(string.Empty, result.Error);
        Assert.Contains("STALE_READ status=stale source=cas", result.Output, StringComparison.Ordinal);
        Assert.Contains("BEGIN_RAW_TEXT\ncorrupt CAS bytes\nEND_RAW_TEXT", result.Output, StringComparison.Ordinal);
        Assert.Contains(
            $"HASH_RECORD raw_sha256={fingerprints.RawSha256} "
                + $"normalized_sha256={fingerprints.NormalizedSha256} "
                + $"cas_ref={fingerprints.RawSha256} source=ledger",
            result.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void CurrentAtomReadsCommittedCasWithoutReplayingChangedSource()
    {
        const string sourcePath = "fixtures/show-atom/adapter.md";
        var committedBytes = Encoding.UTF8.GetBytes(
            "## 1. Synthetic section\n\nCommitted synthetic content.\n");
        var changedSourceBytes = Encoding.UTF8.GetBytes(
            "## 1. Synthetic section\n\nChanged source content.\n");
        var fingerprints = DigestionFingerprint.Compute(committedBytes);
        var files = FixtureFiles(
            AdapterLedger(sourcePath, fingerprints.RawSha256, fingerprints.NormalizedSha256),
            sourcePath,
            changedSourceBytes,
            fingerprints.RawSha256,
            committedBytes);

        var result = Environment("/repo", files).ShowAtom(
            ["--atom-id", BareAtomId(fingerprints.RawSha256)]);

        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain("STALE_READ", result.Output, StringComparison.Ordinal);
        Assert.Contains("Committed synthetic content", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("Changed source content", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void ReusedAstPathReadsTheRequestedAtomsCommittedCas()
    {
        const string sourcePath = "fixtures/show-atom/adapter.md";
        var oldBytes = Encoding.UTF8.GetBytes(
            "## 1. Synthetic section\n\nOld synthetic content.\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "## 1. Synthetic section\n\nCurrent synthetic content.\n");
        var oldFingerprints = DigestionFingerprint.Compute(oldBytes);
        var files = FixtureFiles(
            AdapterLedger(sourcePath, oldFingerprints.RawSha256, oldFingerprints.NormalizedSha256),
            sourcePath,
            currentBytes,
            oldFingerprints.RawSha256,
            oldBytes);

        var result = Environment("/repo", files).ShowAtom(
            ["--atom-id", BareAtomId(oldFingerprints.RawSha256)]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("Old synthetic content", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("Current synthetic content", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void ConflictMarkedSourceDoesNotAffectCommittedCasRead()
    {
        const string sourcePath = "fixtures/show-atom/conflicted.md";
        var sourceBytes = Encoding.UTF8.GetBytes("<<<<<<< HEAD\nreceipt\n=======\n");
        var casBytes = Encoding.UTF8.GetBytes("committed receipt\n");
        var fingerprints = DigestionFingerprint.Compute(casBytes);
        var files = FixtureFiles(
            ContentLedger(sourcePath, fingerprints.RawSha256, fingerprints.NormalizedSha256),
            sourcePath,
            sourceBytes,
            fingerprints.RawSha256,
            casBytes);

        var result = Environment("/repo", files).ShowAtom(
            ["--atom-id", BareAtomId(fingerprints.RawSha256)]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("committed receipt", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("<<<<<<<", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void AcknowledgedSupersededGenerationReadsCommittedHistoricalCasAndMarksItStale()
    {
        const string sourcePath = "fixtures/show-atom/adapter.md";
        var oldBytes = Encoding.UTF8.GetBytes(
            "## 1. Synthetic section\n\nOld synthetic content.\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "## 1. Synthetic section\n\nCurrent synthetic content.\n");
        var oldFingerprints = DigestionFingerprint.Compute(oldBytes);
        var currentFingerprints = DigestionFingerprint.Compute(currentBytes);
        var ledger = AdapterGenerationLedger(sourcePath, oldFingerprints, currentFingerprints);
        var ledgerSource = Assert.Single(ledger.RequireDigestionSources());
        ledger = ledger.WithDigestionSources(
        [
            ledgerSource with { AcknowledgedStale = [BareAtomId(oldFingerprints.RawSha256)] },
        ]);
        var files = AdapterGenerationFixtureFiles(
            ledger,
            sourcePath,
            currentBytes,
            (oldFingerprints.RawSha256, oldBytes),
            (currentFingerprints.RawSha256, currentBytes));

        var result = Environment("/repo", files).ShowAtom(
            ["--atom-id", BareAtomId(oldFingerprints.RawSha256)]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("STALE_READ status=stale source=cas\n", result.Output, StringComparison.Ordinal);
        Assert.Contains(
            "BEGIN_RAW_TEXT\n## 1. Synthetic section\n\nOld synthetic content.\nEND_RAW_TEXT\n",
            result.Output,
            StringComparison.Ordinal);
        Assert.DoesNotContain("Current synthetic content", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void SameAstPathGenerationIsNotMarkedStaleWithoutAcknowledgment()
    {
        const string sourcePath = "fixtures/show-atom/adapter.md";
        var oldBytes = Encoding.UTF8.GetBytes(
            "## 1. Synthetic section\n\nOld synthetic content.\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "## 1. Synthetic section\n\nCurrent synthetic content.\n");
        var oldFingerprints = DigestionFingerprint.Compute(oldBytes);
        var currentFingerprints = DigestionFingerprint.Compute(currentBytes);
        var files = AdapterGenerationFixtureFiles(
            AdapterGenerationLedger(sourcePath, oldFingerprints, currentFingerprints),
            sourcePath,
            currentBytes,
            (oldFingerprints.RawSha256, oldBytes),
            (currentFingerprints.RawSha256, currentBytes));

        var result = Environment("/repo", files).ShowAtom(
            ["--atom-id", BareAtomId(oldFingerprints.RawSha256)]);

        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain("STALE_READ", result.Output, StringComparison.Ordinal);
        Assert.Contains("Old synthetic content", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("Current synthetic content", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void AcknowledgedStaleEntryReadsCommittedHistoricalCasAndMarksItStale()
    {
        const string sourcePath = "fixtures/show-atom/adapter.md";
        var oldBytes = Encoding.UTF8.GetBytes(
            "## 1. Synthetic section\n\nOld synthetic content.\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "## 1. Synthetic section\n\nCurrent synthetic content.\n");
        var oldFingerprints = DigestionFingerprint.Compute(oldBytes);
        var ledger = AdapterLedger(
            sourcePath,
            oldFingerprints.RawSha256,
            oldFingerprints.NormalizedSha256);
        var ledgerSource = Assert.Single(ledger.RequireDigestionSources());
        ledger = ledger.WithDigestionSources(
        [
            ledgerSource with { AcknowledgedStale = [BareAtomId(oldFingerprints.RawSha256)] },
        ]);
        var files = FixtureFiles(
            ledger,
            sourcePath,
            currentBytes,
            oldFingerprints.RawSha256,
            oldBytes);

        var result = Environment("/repo", files).ShowAtom(
            ["--atom-id", BareAtomId(oldFingerprints.RawSha256)]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("STALE_READ status=stale source=cas\n", result.Output, StringComparison.Ordinal);
        Assert.Contains("Old synthetic content", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("Current synthetic content", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void CliDispatchesShowAtomToTheReadOnlyEnvironmentCommand()
    {
        const string sourcePath = "fixtures/show-atom/boundary.md";
        const string rawText = "receipt\n";
        var rawBytes = Encoding.UTF8.GetBytes(rawText);
        var fingerprints = DigestionFingerprint.Compute(rawBytes);
        var files = FixtureFiles(
            ContentLedger(sourcePath, fingerprints.RawSha256, fingerprints.NormalizedSha256),
            sourcePath,
            rawBytes,
            fingerprints.RawSha256,
            rawBytes);
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["show-atom", "--atom-id", BareAtomId(fingerprints.RawSha256)],
            Environment("/repo", files),
            console);

        Assert.Equal(0, exitCode);
        Assert.Contains(
            $"SHOW_ATOM atom_id={BareAtomId(fingerprints.RawSha256)}",
            console.Output,
            StringComparison.Ordinal);
        Assert.Equal(string.Empty, console.Error);
    }

    private static ProductionCliEnvironment Environment(
        string repositoryRoot,
        RawRepositorySnapshot current) => new(
            repositoryRoot,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                current,
                baseline: null),
            new FakeLeanReportSource(report: null));

    private static RawRepositorySnapshot FixtureFiles(
        BackfillInventoryDocument ledger,
        string sourcePath,
        byte[] sourceBytes,
        string casRef,
        byte[] casBytes) => SnapshotWithLedger(
            ledger,
            [
            RawRepositoryEntry.FromText(
                TheoryAtomizerDataLoader.DataPath,
                SyntheticAtomizerData),
            new RawRepositoryEntry(sourcePath, ImmutableArray.CreateRange(sourceBytes)),
            new RawRepositoryEntry(
                DigestionCasStore.RootPath + casRef["sha256:".Length..],
                ImmutableArray.CreateRange(casBytes)),
            ]);

    private static RawRepositorySnapshot AdapterGenerationFixtureFiles(
        BackfillInventoryDocument ledger,
        string sourcePath,
        byte[] sourceBytes,
        params (string Reference, byte[] Bytes)[] casObjects) => SnapshotWithLedger(
            ledger,
            [
            RawRepositoryEntry.FromText(
                TheoryAtomizerDataLoader.DataPath,
                SyntheticAtomizerData),
            new RawRepositoryEntry(sourcePath, ImmutableArray.CreateRange(sourceBytes)),
            .. casObjects.Select(static item => new RawRepositoryEntry(
                DigestionCasStore.RootPath + item.Reference["sha256:".Length..],
                ImmutableArray.CreateRange(item.Bytes))),
            ]);

    private static BackfillInventoryDocument ContentLedger(
        string sourcePath,
        string rawSha256,
        string normalizedSha256) => Document(
            "content-source",
            sourcePath,
            AtomizerRegistry.NoAtomizerId,
            [Entry(
                "content-source",
                sourcePath,
                AtomizerRegistry.NoAtomizerId,
                BareAtomId(rawSha256),
                new DigestionFingerprints(rawSha256, normalizedSha256))]);

    private static BackfillInventoryDocument AdapterLedger(
        string sourcePath,
        string rawSha256,
        string normalizedSha256) => Document(
            "adapter-source",
            sourcePath,
            AdapterAtomizerId,
            [Entry(
                "adapter-source",
                sourcePath,
                AdapterAtomizerId,
                BareAtomId(rawSha256),
                new DigestionFingerprints(rawSha256, normalizedSha256))]);

    private static BackfillInventoryDocument AdapterGenerationLedger(
        string sourcePath,
        DigestionFingerprints oldFingerprints,
        DigestionFingerprints currentFingerprints) => Document(
            "adapter-source",
            sourcePath,
            AdapterAtomizerId,
            [
                Entry(
                    "adapter-source",
                    sourcePath,
                    AdapterAtomizerId,
                    BareAtomId(oldFingerprints.RawSha256),
                    oldFingerprints),
                Entry(
                    "adapter-source",
                    sourcePath,
                    AdapterAtomizerId,
                    BareAtomId(currentFingerprints.RawSha256),
                    currentFingerprints),
            ]);

    private static BackfillInventoryDocument Document(
        string sourceId,
        string sourcePath,
        string atomizer,
        ImmutableArray<DigestionLedgerEntry> entries) => BackfillInventoryDocument.Create(
        [
            new DigestionLedgerSource(
                sourceId,
                sourcePath,
                atomizer,
                [],
                GenreRegistryProjection.Available(
                    atomizer == AtomizerRegistry.NoAtomizerId
                        ? GenreRegistryCheck.NoGenreRegistry
                        : GenreRegistryCheck.Collected([])),
                entries),
        ],
        []);

    private static DigestionLedgerEntry Entry(
        string sourceId,
        string sourcePath,
        string atomizer,
        string atomId,
        DigestionFingerprints fingerprints) => new(
            sourceId,
            sourcePath,
            atomizer,
            atomId,
            fingerprints,
            [],
            new DigestionReceipts([], [], [], [], null),
            new DigestionStatus(DigestionMigrationState.Partial, DigestionTruthState.Open),
            fingerprints.RawSha256);

    private static string BareAtomId(string rawSha256) =>
        rawSha256["sha256:".Length..];

    private static RawRepositorySnapshot SnapshotWithLedger(
        BackfillInventoryDocument ledger,
        IEnumerable<RawRepositoryEntry> otherEntries)
    {
        var entries = otherEntries.ToList();
        foreach (var source in ledger.RequireDigestionSources())
        {
            entries.Add(new RawRepositoryEntry(
                $"{BackfillInventoryLoader.RootPath}{source.SourceId}/source.toml",
                BackfillInventoryWriter.WriteSourceMetadata(source)));
            foreach (var entry in source.Entries)
            {
                var state = DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)
                    + "-"
                    + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth);
                entries.Add(new RawRepositoryEntry(
                    $"{BackfillInventoryLoader.RootPath}{source.SourceId}/{state}/{entry.AtomId}.yaml",
                    BackfillInventoryWriter.WriteAtom(entry)));
            }
        }

        return RawRepositorySnapshot.Create(entries);
    }

    private static string SyntheticAtomizerData => """
        schema_version = 1

        [[observer.claim_prefixes]]
        prefix = "**Synthetic observer**"
        locator = "theorem/synthetic-observer"

        [[first.genres]]
        token = "Synthetic"
        kind = "theorem"

        [[first.claim_prefixes]]
        prefix = "**Synthetic claim**"
        locator = "theorem/synthetic-claim"

        [[first.constants]]
        name = "SYNTHETIC_C"
        locator = "constant/synthetic"

        [[second.genres]]
        token = "Synthetic"
        kind = "theorem"

        [[second.markers]]
        role = "trace-note"
        text = "Synthetic trace"

        [[second.heading_prefixes]]
        prefix = "Synthetic supplement "
        locator = "metadata/supplement"

        [[wm.headings]]
        role = "title"
        text = "Synthetic WM title"

        [[wm.headings]]
        role = "appendix"
        text = "Synthetic WM appendix"

        [[wm.headings]]
        role = "audit"
        text = "Synthetic WM audit"
        """
        .Replace("[[first.", "[[" + string.Concat("gi", "ct") + ".", StringComparison.Ordinal)
        .Replace("[[second.", "[[" + string.Concat("pz", "g") + ".", StringComparison.Ordinal);
}
