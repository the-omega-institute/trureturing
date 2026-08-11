using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ShowAtomTests
{
    private const string BoundaryAtomId = "boundary-atom";
    private const string AdapterAtomId = "adapter-atom";
    private const string AdapterAstPath = "section/1";
    private const string AdapterAtomizerId = AtomizerRegistry.PeriodicTreeId;

    [Fact]
    public void BoundaryAtomPrintsItsByteExactParagraphNormalizedTextAndVerifiedHashesWithoutWriting()
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
        var startByte = Encoding.UTF8.GetByteCount(prefix);
        var files = FixtureFiles(
            BoundaryLedger(sourcePath, startByte, startByte + rawBytes.Length, rawSha256, normalizedSha256),
            sourcePath,
            sourceBytes,
            rawSha256,
            rawBytes);
        using var temporary = new TemporaryDirectory();
        var before = Directory.EnumerateFileSystemEntries(temporary.Path).ToArray();

        var result = Environment(temporary.Path, files).ShowAtom(["--atom-id", BoundaryAtomId]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(string.Empty, result.Error);
        Assert.Contains(
            $"SHOW_ATOM atom_id={BoundaryAtomId} source_id=boundary-source "
                + $"source_path={sourcePath} atomizer={AtomizerRegistry.NoAtomizerId} "
                + "ast_path=sample/01\n",
            result.Output,
            StringComparison.Ordinal);
        Assert.Contains(
            $"HASH_VERIFY raw_sha256={rawSha256} normalized_sha256={normalizedSha256} "
                + $"cas_ref={rawSha256} status=match\n",
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
    public void RegisteredAtomizerReplaysTheSourceAndPrintsTheKnownAtomParagraph()
    {
        const string sourcePath = "fixtures/show-atom/adapter.md";
        const string rawText = "## 1. Synthetic section\r\n\r\nCafe\u0301 receipt.\r\n";
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Synthetic document\r\n\r\n" + rawText);
        var rawBytes = Encoding.UTF8.GetBytes(rawText);
        var fingerprints = DigestionFingerprint.Compute(rawBytes);
        var files = FixtureFiles(
            AdapterLedger(
                sourcePath,
                fingerprints.RawSha256,
                fingerprints.NormalizedSha256),
            sourcePath,
            sourceBytes,
            fingerprints.RawSha256,
            rawBytes);

        var result = Environment("/repo", files).ShowAtom(["--atom-id", AdapterAtomId]);

        Assert.True(result.Success, result.Error);
        Assert.Contains(
            $"atomizer={AdapterAtomizerId} ast_path={AdapterAstPath}\n",
            result.Output,
            StringComparison.Ordinal);
        Assert.Contains($"BEGIN_RAW_TEXT\n{rawText}END_RAW_TEXT\n", result.Output, StringComparison.Ordinal);
        Assert.Contains(
            "BEGIN_NORMALIZED_TEXT\n## 1. Synthetic section\n\n"
                + "Caf\u00e9 receipt.\nEND_NORMALIZED_TEXT\n",
            result.Output,
            StringComparison.Ordinal);
        Assert.Contains(
            $"HASH_VERIFY raw_sha256={fingerprints.RawSha256} "
                + $"normalized_sha256={fingerprints.NormalizedSha256} "
                + $"cas_ref={fingerprints.RawSha256} status=match\n",
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
            BoundaryLedger(sourcePath, 0, rawBytes.Length, fingerprints.RawSha256, fingerprints.NormalizedSha256),
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
            BoundaryLedger(sourcePath, 0, rawBytes.Length, fingerprints.RawSha256, fingerprints.NormalizedSha256),
            sourcePath,
            rawBytes,
            fingerprints.RawSha256,
            rawBytes);

        var result = Environment("/repo", files).ShowAtom(["--atom-id", BoundaryAtomId]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("BEGIN_RAW_TEXT\nreceipt\r\nEND_RAW_TEXT\n", result.Output, StringComparison.Ordinal);
        Assert.Contains(
            "BEGIN_NORMALIZED_TEXT\nreceipt\nEND_NORMALIZED_TEXT\n",
            result.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void CasBlobHashMismatchFailsClosedBeforePrintingText()
    {
        const string sourcePath = "fixtures/show-atom/adapter.md";
        const string rawText = "## 1. Synthetic section\n\nSynthetic claim.\n";
        var rawBytes = Encoding.UTF8.GetBytes(rawText);
        var fingerprints = DigestionFingerprint.Compute(rawBytes);
        var files = FixtureFiles(
            AdapterLedger(sourcePath, fingerprints.RawSha256, fingerprints.NormalizedSha256),
            sourcePath,
            rawBytes,
            fingerprints.RawSha256,
            Encoding.UTF8.GetBytes("corrupt CAS bytes\n"));

        var result = Environment("/repo", files).ShowAtom(["--atom-id", AdapterAtomId]);

        Assert.False(result.Success);
        Assert.Equal(string.Empty, result.Output);
        Assert.Contains(
            $"SHOW_ATOM_INVALID atom {AdapterAtomId} CAS blob hash mismatch",
            result.Error,
            StringComparison.Ordinal);
    }

    [Fact]
    public void ReusedAstPathWithDifferentContentFailsClosedInsteadOfShowingAnotherAtom()
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

        var result = Environment("/repo", files).ShowAtom(["--atom-id", AdapterAtomId]);

        Assert.False(result.Success);
        Assert.Equal(string.Empty, result.Output);
        Assert.Contains(
            $"SHOW_ATOM_INVALID atom {AdapterAtomId} raw hash mismatch",
            result.Error,
            StringComparison.Ordinal);
        Assert.DoesNotContain("current", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void SupersededGenerationReadsStrictlyVerifiedHistoricalCasAndMarksItStale()
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

        var result = Environment("/repo", files).ShowAtom(["--atom-id", AdapterAtomId]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("STALE_READ status=stale source=cas\n", result.Output, StringComparison.Ordinal);
        Assert.Contains(
            "BEGIN_RAW_TEXT\n## 1. Synthetic section\n\nOld synthetic content.\nEND_RAW_TEXT\n",
            result.Output,
            StringComparison.Ordinal);
        Assert.DoesNotContain("Current synthetic content", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void AcknowledgedStaleEntryReadsStrictlyVerifiedHistoricalCasAndMarksItStale()
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
                oldFingerprints.NormalizedSha256)
            .Replace(
                $"    atomizer: {AdapterAtomizerId}\n",
                $"    atomizer: {AdapterAtomizerId}\n"
                    + "    acknowledged_stale:\n"
                    + $"      - {AdapterAtomId}\n",
                StringComparison.Ordinal);
        var files = FixtureFiles(
            ledger,
            sourcePath,
            currentBytes,
            oldFingerprints.RawSha256,
            oldBytes);

        var result = Environment("/repo", files).ShowAtom(["--atom-id", AdapterAtomId]);

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
            BoundaryLedger(sourcePath, 0, rawBytes.Length, fingerprints.RawSha256, fingerprints.NormalizedSha256),
            sourcePath,
            rawBytes,
            fingerprints.RawSha256,
            rawBytes);
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["show-atom", "--atom-id", BoundaryAtomId],
            Environment("/repo", files),
            console);

        Assert.Equal(0, exitCode);
        Assert.Contains($"SHOW_ATOM atom_id={BoundaryAtomId}", console.Output, StringComparison.Ordinal);
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
        string ledger,
        string sourcePath,
        byte[] sourceBytes,
        string casRef,
        byte[] casBytes) => RawRepositorySnapshot.Create(
        [
            RawRepositoryEntry.FromText(BackfillInventoryLoader.RelativePath, ledger),
            RawRepositoryEntry.FromText(
                TheoryAtomizerDataLoader.DataPath,
                SyntheticAtomizerData),
            new RawRepositoryEntry(sourcePath, ImmutableArray.CreateRange(sourceBytes)),
            new RawRepositoryEntry(
                DigestionCasStore.RootPath + casRef["sha256:".Length..],
                ImmutableArray.CreateRange(casBytes)),
        ]);

    private static RawRepositorySnapshot AdapterGenerationFixtureFiles(
        string ledger,
        string sourcePath,
        byte[] sourceBytes,
        params (string Reference, byte[] Bytes)[] casObjects) => RawRepositorySnapshot.Create(
        [
            RawRepositoryEntry.FromText(BackfillInventoryLoader.RelativePath, ledger),
            RawRepositoryEntry.FromText(
                TheoryAtomizerDataLoader.DataPath,
                SyntheticAtomizerData),
            new RawRepositoryEntry(sourcePath, ImmutableArray.CreateRange(sourceBytes)),
            .. casObjects.Select(static item => new RawRepositoryEntry(
                DigestionCasStore.RootPath + item.Reference["sha256:".Length..],
                ImmutableArray.CreateRange(item.Bytes))),
        ]);

    private static string BoundaryLedger(
        string sourcePath,
        int startByte,
        int endByte,
        string rawSha256,
        string normalizedSha256) => $$"""
        schema_version: 3
        ledger: theory-digestion-v1
        sources:
          - source_id: boundary-source
            path: {{sourcePath}}
            atomizer: {{AtomizerRegistry.NoAtomizerId}}
            entries:
              - atom_id: {{BoundaryAtomId}}
                boundary:
                  ast_path: sample/01
                  start_byte: {{startByte}}
                  end_byte: {{endByte}}
                fingerprints:
                  raw_sha256: {{rawSha256}}
                  normalized_sha256: {{normalizedSha256}}
                cas_ref: {{rawSha256}}
                coverage_gids: []
                receipts:
                  coverage: []
                  scribe: []
                  unresolved_subitems: []
                status:
                  migration: partial
                  truth: open
        ticket_index: []
        """;

    private static string AdapterLedger(
        string sourcePath,
        string rawSha256,
        string normalizedSha256) => $$"""
        schema_version: 3
        ledger: theory-digestion-v1
        sources:
          - source_id: adapter-source
            path: {{sourcePath}}
            atomizer: {{AdapterAtomizerId}}
            entries:
              - atom_id: {{AdapterAtomId}}
                ast_path: {{AdapterAstPath}}
                fingerprints:
                  raw_sha256: {{rawSha256}}
                  normalized_sha256: {{normalizedSha256}}
                cas_ref: {{rawSha256}}
                coverage_gids: []
                receipts:
                  coverage: []
                  scribe: []
                  unresolved_subitems: []
                status:
                  migration: partial
                  truth: open
        ticket_index: []
        """;

    private static string AdapterGenerationLedger(
        string sourcePath,
        DigestionFingerprints oldFingerprints,
        DigestionFingerprints currentFingerprints) => $$"""
        schema_version: 3
        ledger: theory-digestion-v1
        sources:
          - source_id: adapter-source
            path: {{sourcePath}}
            atomizer: {{AdapterAtomizerId}}
            entries:
              - atom_id: {{AdapterAtomId}}
                ast_path: {{AdapterAstPath}}
                fingerprints:
                  raw_sha256: {{oldFingerprints.RawSha256}}
                  normalized_sha256: {{oldFingerprints.NormalizedSha256}}
                cas_ref: {{oldFingerprints.RawSha256}}
                coverage_gids: []
                receipts:
                  coverage: []
                  scribe: []
                  unresolved_subitems: []
                status:
                  migration: partial
                  truth: open
              - atom_id: adapter-current
                ast_path: {{AdapterAstPath}}
                fingerprints:
                  raw_sha256: {{currentFingerprints.RawSha256}}
                  normalized_sha256: {{currentFingerprints.NormalizedSha256}}
                cas_ref: {{currentFingerprints.RawSha256}}
                coverage_gids: []
                receipts:
                  coverage: []
                  scribe: []
                  unresolved_subitems: []
                status:
                  migration: partial
                  truth: open
        ticket_index: []
        """;

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
