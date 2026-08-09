using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record DigestionIngestPlan(
    BackfillInventoryDocument Document,
    int StaleAcknowledged,
    int ResidualOpenAdded,
    ImmutableArray<DigestionCasObject> CasObjects,
    ImmutableArray<DigestionIngestFallback> Fallbacks);

internal static class DigestionIngestor
{
    internal static DigestionIngestPlan Plan(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        BackfillInventoryDocument baselineDocument)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(baselineDocument);

        var alignment = DigestionLedgerAligner.Evaluate(
            document,
            snapshot,
            baselineDocument,
            DigestionAlignmentMode.Ingest);
        if (alignment.Findings.Length > 0)
        {
            throw new FormatException(
                "ingest alignment is invalid: " + string.Join("; ", alignment.Findings));
        }

        var stale = alignment.ActualStale.ToHashSet(StringComparer.Ordinal);
        var residualBySource = alignment.Residual
            .GroupBy(static item => item.SourceId, StringComparer.Ordinal)
            .ToDictionary(static group => group.Key, static group => group.ToArray(), StringComparer.Ordinal);
        var atomIds = document.RequireDigestionEntries()
            .Select(static entry => entry.AtomId)
            .ToHashSet(StringComparer.Ordinal);
        var sources = ImmutableArray.CreateBuilder<DigestionLedgerSource>();
        var casObjects = new Dictionary<string, DigestionCasObject>(StringComparer.Ordinal);
        var staleAcknowledged = 0;
        var residualOpenAdded = 0;
        foreach (var source in document.RequireDigestionSources())
        {
            if (!AtomizerRegistry.IsRegistered(source.Atomizer))
            {
                if (source.Atomizer != AtomizerRegistry.NoAtomizerId)
                {
                    throw new FormatException($"ingest source {source.SourceId} has unknown atomizer {source.Atomizer}");
                }

                // 无 atomizer 的源(手工编写的条目)没有可再派生的东西:原样透传。
                // 字节偏移废除前,这里要 CaptureBoundarySource 把 boundary 折成 CAS;
                // 现在条目已自带 cas_ref,透传即可 —— 但**不能没有这条分支**:
                // 缺了它,整个 golden-ledger-spec 源(12 条有覆盖的条目)会被静默丢弃。
                sources.Add(source);
                continue;
            }

            var acknowledgments = source.Entries
                .Where(entry => stale.Contains(entry.AtomId))
                .Select(static entry => entry.AtomId)
                .Order(StringComparer.Ordinal)
                .ToImmutableArray();
            var priorAcknowledgments = source.AcknowledgedStale.ToHashSet(StringComparer.Ordinal);
            staleAcknowledged += acknowledgments.Count(priorAcknowledgment =>
                !priorAcknowledgments.Contains(priorAcknowledgment));
            var entries = source.Entries.ToBuilder();
            if (residualBySource.TryGetValue(source.SourceId, out var residual))
            {
                foreach (var item in residual)
                {
                    if (!atomIds.Add(item.SuggestedAtomId))
                    {
                        throw new FormatException(
                            $"ingest residual atom_id collides with the ledger: {item.SuggestedAtomId}");
                    }

                    var captured = AddCasObject(item.Atom.RawBytes.AsSpan(), casObjects);
                    entries.Add(new DigestionLedgerEntry(
                        source.SourceId,
                        source.SourcePath,
                        source.Atomizer,
                        item.SuggestedAtomId,
                        item.Atom.AstPath,
                        item.Atom.Fingerprints,
                        CoverageGids: [],
                        new DigestionReceipts([], [], []),
                        item.ProjectedStatus,
                        ReceiptSyntax: null,
                        CasRef: captured.Reference));
                    residualOpenAdded++;
                }
            }

            sources.Add(source with
            {
                AcknowledgedStale = acknowledgments,
                Entries = entries.ToImmutable(),
            });
        }

        return new DigestionIngestPlan(
            document.WithDigestionSources(sources.ToImmutable()),
            staleAcknowledged,
            residualOpenAdded,
            casObjects.Values
                .OrderBy(static item => item.RelativePath, StringComparer.Ordinal)
                .ToImmutableArray(),
            alignment.Fallbacks);
    }

    private static DigestionCasObject AddCasObject(
        ReadOnlySpan<byte> bytes,
        IDictionary<string, DigestionCasObject> casObjects)
    {
        var captured = DigestionCasStore.Capture(bytes);
        if (casObjects.TryGetValue(captured.Reference, out var existing))
        {
            if (!existing.Bytes.AsSpan().SequenceEqual(captured.Bytes.AsSpan()))
            {
                throw new FormatException($"ingest CAS collision at {captured.Reference}");
            }

            return existing;
        }

        casObjects.Add(captured.Reference, captured);
        return captured;
    }

}
