using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ShowAtomTests
{
    private const string BoundaryAtomId = "boundary-atom";
    private const string AdapterAtomId = "adapter-atom";

    [Fact]
    public void BoundaryAtomPrintsItsByteExactParagraphNormalizedTextAndVerifiedHashesWithoutWriting()
    {
        const string sourcePath = "docs/spec.md";
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
                + $"source_path={sourcePath} atomizer=none ast_path=sample/01\n",
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
        const string sourcePath = "docs/gict.md";
        const string rawText = "**定理 7.15(G 轴质量)**。Cafe\u0301。\r\n";
        const string rawSha256 =
            "sha256:fd658122b0ad389ef8244881a9652cda679c3d63cc7fa03533521138ebb9c45a";
        const string normalizedSha256 =
            "sha256:0a74299c7f4664ef8fea8ec7428ac01cd4c248348c16b4e22580f361ec8e16fb";
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# GICT\r\n\r\n## VII.7 接口\r\n\r\n" + rawText);
        var rawBytes = Encoding.UTF8.GetBytes(rawText);
        var files = FixtureFiles(
            AdapterLedger(sourcePath, rawSha256, normalizedSha256),
            sourcePath,
            sourceBytes,
            rawSha256,
            rawBytes);

        var result = Environment("/repo", files).ShowAtom(["--atom-id", AdapterAtomId]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("atomizer=gict-v1 ast_path=theorem/7.15\n", result.Output, StringComparison.Ordinal);
        Assert.Contains($"BEGIN_RAW_TEXT\n{rawText}END_RAW_TEXT\n", result.Output, StringComparison.Ordinal);
        Assert.Contains(
            "BEGIN_NORMALIZED_TEXT\n**定理 7.15(G 轴质量)**。Caf\u00e9。\nEND_NORMALIZED_TEXT\n",
            result.Output,
            StringComparison.Ordinal);
        Assert.Contains(
            $"HASH_VERIFY raw_sha256={rawSha256} normalized_sha256={normalizedSha256} "
                + $"cas_ref={rawSha256} status=match\n",
            result.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void MissingAtomFailsClosedWithoutOutput()
    {
        const string sourcePath = "docs/spec.md";
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
        const string sourcePath = "docs/spec.md";
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
        const string sourcePath = "docs/gict.md";
        const string rawText = "**定理 7.15(G 轴质量)**。claim。\n";
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
        const string sourcePath = "docs/gict.md";
        var oldBytes = Encoding.UTF8.GetBytes("**定理 7.15(G 轴质量)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("**定理 7.15(G 轴质量)**。current。\n");
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
    public void CliDispatchesShowAtomToTheReadOnlyEnvironmentCommand()
    {
        const string sourcePath = "docs/spec.md";
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
            new RawRepositoryEntry(sourcePath, ImmutableArray.CreateRange(sourceBytes)),
            new RawRepositoryEntry(
                DigestionCasStore.RootPath + casRef["sha256:".Length..],
                ImmutableArray.CreateRange(casBytes)),
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
            atomizer: none
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
            atomizer: gict-v1
            entries:
              - atom_id: {{AdapterAtomId}}
                ast_path: theorem/7.15
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
}
