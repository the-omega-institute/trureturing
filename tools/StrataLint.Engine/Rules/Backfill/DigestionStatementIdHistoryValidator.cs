using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class DigestionStatementIdHistoryValidator
{
    internal static bool IsAffectedBy(RawChangeSet? changes) =>
        changes is null
        || changes.Paths.Any(static path =>
            BackfillInventoryLoader.IsCanonicalPath(path.Value)
            && path.Value.EndsWith(".yaml", StringComparison.Ordinal));

    internal static ImmutableArray<string> Validate(
        BackfillInventoryDocument protectedBaseDocument,
        BackfillInventoryDocument candidateDocument,
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidate,
        RawChangeSet? changes)
    {
        ArgumentNullException.ThrowIfNull(protectedBaseDocument);
        ArgumentNullException.ThrowIfNull(candidateDocument);
        ArgumentNullException.ThrowIfNull(protectedBase);
        ArgumentNullException.ThrowIfNull(candidate);
        if (!IsAffectedBy(changes))
        {
            return [];
        }

        var findings = ImmutableArray.CreateBuilder<string>();
        var baseEntries = EntriesByAtomId(protectedBaseDocument, "protected base", findings);
        var candidateEntries = EntriesByAtomId(candidateDocument, "candidate", findings);
        var affectedAtomIds = AffectedAtomIds(baseEntries, candidateEntries, changes);
        FrozenStatementIndex? baseStatements = null;
        EffectiveLeanPins? basePins = null;
        EffectiveLeanPins? candidatePins = null;

        foreach (var atomId in affectedAtomIds.Order(StringComparer.Ordinal))
        {
            baseEntries.TryGetValue(atomId, out var baseEntry);
            candidateEntries.TryGetValue(atomId, out var candidateEntry);
            if (candidateEntry is null)
            {
                if (baseEntry is not null
                    && baseEntry.Receipts.Coverage.Any(static receipt =>
                        !receipt.StatementIdHistory.IsDefaultOrEmpty))
                {
                    findings.Add($"entry {atomId} removed append-only statement_id_history");
                }

                continue;
            }

            var baseReceipts = ReceiptsByGid(baseEntry, "protected base", findings);
            var candidateReceipts = ReceiptsByGid(candidateEntry, "candidate", findings);
            foreach (var (gid, receipt) in candidateReceipts.OrderBy(
                         static item => item.Key,
                         StringComparer.Ordinal))
            {
                var candidateHistory = History(receipt);
                if (!baseReceipts.TryGetValue(gid, out var baseReceipt))
                {
                    if (!candidateHistory.IsEmpty)
                    {
                        findings.Add(
                            $"entry {atomId} receipt {gid} invents statement_id_history without a protected-base receipt");
                    }

                    continue;
                }

                var baseHistory = History(baseReceipt);
                if (candidateHistory.Length < baseHistory.Length
                    || !candidateHistory.Take(baseHistory.Length).SequenceEqual(baseHistory))
                {
                    findings.Add(
                        $"entry {atomId} receipt {gid} mutates or truncates append-only statement_id_history");
                    continue;
                }

                if (receipt.TargetStatementId == baseReceipt.TargetStatementId)
                {
                    if (candidateHistory.Length != baseHistory.Length)
                    {
                        findings.Add(
                            $"entry {atomId} receipt {gid} appends statement_id_history without target_statement_id drift");
                    }

                    continue;
                }

                if (candidateHistory.Length != baseHistory.Length + 1)
                {
                    findings.Add(
                        $"entry {atomId} receipt {gid} target_statement_id drift requires exactly one history append");
                    continue;
                }

                var appended = candidateHistory[^1];
                if (appended.StatementId != baseReceipt.TargetStatementId)
                {
                    findings.Add(
                        $"entry {atomId} receipt {gid} history statement_id does not equal the protected-base receipt target");
                    continue;
                }

                if (!Gid.TryParse(gid, out var parsedGid))
                {
                    findings.Add($"entry {atomId} receipt {gid} history GID is invalid");
                    continue;
                }

                baseStatements ??= FrozenStatementIndex.Load(protectedBase);
                if (!baseStatements.TryResolve(parsedGid, out var activeStatement, out _)
                    || activeStatement!.Value != appended.StatementId)
                {
                    findings.Add(
                        $"entry {atomId} receipt {gid} history statement_id is not active in the protected-base frozen ledger");
                    continue;
                }

                if (basePins is null
                    && !EffectiveLeanPins.TryRead(protectedBase, out basePins)
                    || candidatePins is null
                    && !EffectiveLeanPins.TryRead(candidate, out candidatePins)
                    || basePins == candidatePins
                    || appended.EnvironmentPin != basePins
                    || appended.SupersededByPin != candidatePins)
                {
                    findings.Add(
                        $"entry {atomId} receipt {gid} history pins do not match the protected-base and candidate EffectiveLeanPins");
                }
            }

            foreach (var (gid, baseReceipt) in baseReceipts)
            {
                if (!candidateReceipts.ContainsKey(gid)
                    && !History(baseReceipt).IsEmpty)
                {
                    findings.Add(
                        $"entry {atomId} receipt {gid} removed append-only statement_id_history");
                }
            }
        }

        return findings.ToImmutable();
    }

    private static Dictionary<string, DigestionLedgerEntry> EntriesByAtomId(
        BackfillInventoryDocument document,
        string side,
        ImmutableArray<string>.Builder findings)
    {
        var entries = new Dictionary<string, DigestionLedgerEntry>(StringComparer.Ordinal);
        foreach (var entry in document.RequireDigestionEntries())
        {
            if (!entries.TryAdd(entry.AtomId, entry))
            {
                findings.Add($"{side} has duplicate atom_id {entry.AtomId}; statement_id_history cannot be validated");
            }
        }

        return entries;
    }

    private static Dictionary<string, DigestionCoverageReceipt> ReceiptsByGid(
        DigestionLedgerEntry? entry,
        string side,
        ImmutableArray<string>.Builder findings)
    {
        var receipts = new Dictionary<string, DigestionCoverageReceipt>(StringComparer.Ordinal);
        if (entry is null)
        {
            return receipts;
        }

        foreach (var receipt in entry.Receipts.Coverage)
        {
            if (!receipts.TryAdd(receipt.Gid, receipt))
            {
                findings.Add(
                    $"{side} entry {entry.AtomId} has duplicate receipt GID {receipt.Gid}; statement_id_history cannot be validated");
            }
        }

        return receipts;
    }

    private static HashSet<string> AffectedAtomIds(
        IReadOnlyDictionary<string, DigestionLedgerEntry> baseEntries,
        IReadOnlyDictionary<string, DigestionLedgerEntry> candidateEntries,
        RawChangeSet? changes)
    {
        if (changes is null)
        {
            return baseEntries.Keys.Concat(candidateEntries.Keys).ToHashSet(StringComparer.Ordinal);
        }

        var changedPaths = changes.Paths.Select(static path => path.Value).ToHashSet(StringComparer.Ordinal);
        return baseEntries.Values.Concat(candidateEntries.Values)
            .Where(entry => changedPaths.Contains(CanonicalPath(entry)))
            .Select(static entry => entry.AtomId)
            .ToHashSet(StringComparer.Ordinal);
    }

    private static string CanonicalPath(DigestionLedgerEntry entry) =>
        $"{BackfillInventoryLoader.RootPath}{entry.SourceId}/"
        + $"{DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)}-"
        + $"{DigestionStatusNames.Truth(entry.ProjectedStatus.Truth)}/"
        + $"{entry.AtomId}.yaml";

    private static ImmutableArray<DigestionStatementIdHistoryEntry> History(
        DigestionCoverageReceipt receipt) =>
        receipt.StatementIdHistory.IsDefault
            ? []
            : receipt.StatementIdHistory;
}
