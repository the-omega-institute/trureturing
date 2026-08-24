using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class LedgerWriteReceiptIntegrityGate
{
    private readonly record struct GapIdentity(string AtomId, string Detail);

    private sealed record BaselineGapSet(
        HashSet<GapIdentity> Coverage,
        HashSet<GapIdentity> ScribeDefinition,
        HashSet<GapIdentity> ScribeEmission)
    {
        internal bool Contains(string code, GapIdentity identity) => code switch
        {
            "coverage-receipt-mismatch" => Coverage.Contains(identity),
            "scribe-definition-mismatch" => ScribeDefinition.Contains(identity),
            "scribe-emission-mismatch" => ScribeEmission.Contains(identity),
            _ => false,
        };
    }

    internal static void RequireNoNewFailures(
        DigestionLedgerEvaluation evaluation,
        BackfillInventoryDocument baselineDocument,
        RepositorySnapshot baselineSnapshot)
    {
        var baselineGaps = BaselineGapIdentities(baselineDocument, baselineSnapshot);
        var newGaps = evaluation.ReceiptIntegrityGaps
            .Where(item => !baselineGaps.Contains(
                item.Gap.Code,
                new GapIdentity(item.Entry.AtomId, item.Gap.Detail)))
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
            return;
        }

        throw new InvalidOperationException(
            "digest status is invalid: "
            + string.Join("; ", newGaps.Select(static item =>
                $"{item.Entry.AtomId}:{item.Gap.Code}:{item.Gap.Detail}")));
    }

    private static BaselineGapSet BaselineGapIdentities(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot)
    {
        var coverageGaps = new HashSet<GapIdentity>();
        var scribeDefinitionGaps = new HashSet<GapIdentity>();
        var scribeEmissionGaps = new HashSet<GapIdentity>();
        foreach (var entry in document.RequireDigestionEntries())
        {
            var coverageReceipts = FirstReceiptByGid(
                entry.Receipts.Coverage,
                static receipt => receipt.Gid);
            var scribeReceipts = FirstReceiptByGid(
                entry.Receipts.Scribe,
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

                if (!scribeReceipts.TryGetValue(gid, out var scribe))
                {
                    continue;
                }

                var documentGid = ScribeEmissionAttestation.DocumentGid(gid);
                if (ExistingFileHashDiffers(
                        snapshot,
                        ScribeEmissionAttestation.DefinitionPath(documentGid),
                        scribe.DefinitionSha256))
                {
                    scribeDefinitionGaps.Add(identity);
                }

                if (ExistingFileHashDiffers(
                        snapshot,
                        ScribeEmissionAttestation.EmissionPath(documentGid),
                        scribe.EmissionSha256))
                {
                    scribeEmissionGaps.Add(identity);
                }
            }
        }

        return new BaselineGapSet(coverageGaps, scribeDefinitionGaps, scribeEmissionGaps);
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

    private static bool ExistingFileHashDiffers(
        RepositorySnapshot snapshot,
        string path,
        string expectedSha256) =>
        snapshot.TryGetFile(path, out var file)
        && DigestionFingerprint.Compute(file.RawBytes.AsSpan()).RawSha256 != expectedSha256;
}
