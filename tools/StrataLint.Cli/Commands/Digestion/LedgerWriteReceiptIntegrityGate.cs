using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class LedgerWriteReceiptIntegrityGate
{
    private readonly record struct GapIdentity(string AtomId, string Detail);

    internal static int RequireNoNewFailures(
        DigestionLedgerEvaluation evaluation,
        BackfillInventoryDocument baselineDocument,
        RepositorySnapshot baselineSnapshot,
        RepositorySnapshot candidateSnapshot)
    {
        var baselineCoverageGaps = BaselineCoverageGapIdentities(
            baselineDocument,
            baselineSnapshot);
        var baselineEntries = baselineDocument.RequireDigestionEntries()
            .GroupBy(static entry => entry.AtomId, StringComparer.Ordinal)
            .Where(static group => group.Count() == 1)
            .ToDictionary(
                static group => group.Key,
                static group => group.Single(),
                StringComparer.Ordinal);
        var gaps = evaluation.ReceiptIntegrityGaps.ToArray();
        var newGaps = gaps.Where(item => !CanIgnoreBacklogGap(
                item.Entry,
                item.Gap,
                baselineEntries,
                baselineCoverageGaps,
                baselineSnapshot,
                candidateSnapshot))
            .ToArray();
        if (evaluation.Findings.Length > 0)
        {
            throw new InvalidOperationException(
                "digest status is invalid: "
                + string.Join("; ", evaluation.Findings.Concat(newGaps.Select(static item =>
                    $"{item.Entry.AtomId}:{item.Gap.Code}:{item.Gap.Detail}"))));
        }

        if (newGaps.Length == 0)
        {
            return gaps.Length;
        }

        throw new InvalidOperationException(
            "digest status is invalid: "
            + string.Join("; ", newGaps.Select(static item =>
                $"{item.Entry.AtomId}:{item.Gap.Code}:{item.Gap.Detail}")));
    }

    private static bool CanIgnoreBacklogGap(
        DigestionLedgerEntry entry,
        DigestionGap gap,
        IReadOnlyDictionary<string, DigestionLedgerEntry> baselineEntries,
        IReadOnlySet<GapIdentity> baselineCoverageGaps,
        RepositorySnapshot baselineSnapshot,
        RepositorySnapshot candidateSnapshot)
    {
        var identity = new GapIdentity(entry.AtomId, gap.Detail);
        if (gap.Code == "coverage-receipt-mismatch")
        {
            return baselineCoverageGaps.Contains(identity);
        }

        if (gap.Code is not ("scribe-definition-mismatch" or "scribe-emission-mismatch")
            || !baselineEntries.TryGetValue(entry.AtomId, out var baselineEntry))
        {
            return false;
        }

        // Scribe has no baseline verifier fact here. The tracked Markdown is therefore never
        // compared with the receipt; byte equality only limits this separate allowance to a
        // receipt and document tuple the candidate did not touch.
        var candidateReceipts = entry.Receipts.Scribe
            .Where(receipt => string.Equals(receipt.Gid, gap.Detail, StringComparison.Ordinal))
            .ToArray();
        var baselineReceipts = baselineEntry.Receipts.Scribe
            .Where(receipt => string.Equals(receipt.Gid, gap.Detail, StringComparison.Ordinal))
            .ToArray();
        if (candidateReceipts.Length != 1
            || baselineReceipts.Length != 1
            || candidateReceipts[0] != baselineReceipts[0]
            || entry.Fingerprints != baselineEntry.Fingerprints
            || !Gid.TryParse(gap.Detail, out var gid))
        {
            return false;
        }

        var documentGid = ScribeEmissionAttestation.DocumentGid(gap.Detail);
        return ScribeSurfaceUntouched(baselineSnapshot, candidateSnapshot)
            && FileBytesIdentical(
                baselineSnapshot,
                candidateSnapshot,
                ScribeEmissionAttestation.DefinitionPath(documentGid))
            && FileBytesIdentical(
                baselineSnapshot,
                candidateSnapshot,
                ScribeEmissionAttestation.EmissionPath(documentGid))
            && FileBytesIdentical(baselineSnapshot, candidateSnapshot, gid.Path.Value);
    }

    private static bool ScribeSurfaceUntouched(
        RepositorySnapshot baseline,
        RepositorySnapshot candidate) =>
        baseline.Files.Keys
            .Concat(candidate.Files.Keys)
            .Distinct()
            .Where(static path => IsPotentialScribeInput(path.Value))
            .All(path => FileBytesIdentical(baseline, candidate, path.Value));

    private static bool IsPotentialScribeInput(string path)
    {
        if (path.StartsWith("Blueprint/", StringComparison.Ordinal)
            && path.EndsWith(".scribe.cs", StringComparison.Ordinal)
            || path.StartsWith("D5/", StringComparison.Ordinal)
            && path.EndsWith(".lean", StringComparison.Ordinal)
            || path.StartsWith("Library/", StringComparison.Ordinal)
            || path.StartsWith("Problems/", StringComparison.Ordinal)
            || path.StartsWith("Golden/Projection/", StringComparison.Ordinal)
            || path.StartsWith("tools/StrataLint.Scribe/", StringComparison.Ordinal)
            || path.StartsWith("tools/StrataLint.Engine/", StringComparison.Ordinal)
            || path.StartsWith("tools/Trureturing.Truth/", StringComparison.Ordinal)
            || path.StartsWith("tools/lean-inspector/", StringComparison.Ordinal)
            || path == "tools/StrataLint.Cli/Runtime/ScribeEmissionVerifier.cs"
            || path == "tools/scripts/report/lean-report-input.sh"
            || path == "tools/scripts/workflow/scribe-content-checks.sh")
        {
            return true;
        }

        var fileName = path[(path.LastIndexOf('/') + 1)..];
        return path == "Trureturing.lean"
            || path is "lean-toolchain" or "lake-manifest.json" or "lakefile.toml" or "lakefile.lean"
            || fileName == "global.json"
            || fileName.StartsWith("Directory.Build.", StringComparison.Ordinal)
            || fileName.StartsWith("Directory.Packages.", StringComparison.Ordinal)
            || fileName.Equals("NuGet.Config", StringComparison.OrdinalIgnoreCase);
    }

    private static HashSet<GapIdentity> BaselineCoverageGapIdentities(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot)
    {
        var coverageGaps = new HashSet<GapIdentity>();
        foreach (var entry in document.RequireDigestionEntries())
        {
            var coverageReceipts = FirstReceiptByGid(
                entry.Receipts.Coverage,
                static receipt => receipt.Gid);
            foreach (var gid in entry.CoverageGids.Distinct(StringComparer.Ordinal))
            {
                var identity = new GapIdentity(entry.AtomId, gid);
                if (coverageReceipts.TryGetValue(gid, out var coverage)
                    && (coverage.SourceSha256 != entry.Fingerprints.RawSha256
                        || !Gid.TryParse(gid, out var parsedGid)
                        || FileHashDiffers(snapshot, parsedGid.Path.Value, coverage.TargetSha256)))
                {
                    coverageGaps.Add(identity);
                }
            }
        }

        return coverageGaps;
    }

    private static Dictionary<string, T> FirstReceiptByGid<T>(
        IEnumerable<T> receipts,
        Func<T, string> gid)
    {
        var result = new Dictionary<string, T>(StringComparer.Ordinal);
        foreach (var receipt in receipts)
        {
            result.TryAdd(gid(receipt), receipt);
        }

        return result;
    }

    private static bool FileHashDiffers(
        RepositorySnapshot snapshot,
        string path,
        string expectedSha256) =>
        !snapshot.TryGetFile(path, out var file)
        || DigestionFingerprint.Compute(file.RawBytes.AsSpan()).RawSha256 != expectedSha256;

    private static bool FileBytesIdentical(
        RepositorySnapshot baseline,
        RepositorySnapshot candidate,
        string path) =>
        baseline.TryGetFile(path, out var baselineFile)
        && candidate.TryGetFile(path, out var candidateFile)
        && baselineFile.RawBytes.AsSpan().SequenceEqual(candidateFile.RawBytes.AsSpan());
}
