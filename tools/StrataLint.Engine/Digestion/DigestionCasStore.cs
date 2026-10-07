using System.Collections.Immutable;
using System.Security.Cryptography;

namespace StrataLint.Engine;

internal sealed record DigestionCasObject(
    string Reference,
    string RelativePath,
    ImmutableArray<byte> Bytes);

internal sealed record DigestionCasEvaluation(
    ImmutableArray<string> Findings,
    ImmutableHashSet<string> ValidAtomIds,
    ImmutableArray<RawChange>? EvaluatedChanges)
{
    internal bool Matches(RawChangeSet? changes) =>
        changes is null
            ? EvaluatedChanges is null
            : EvaluatedChanges is { } evaluated
                && evaluated.SequenceEqual(changes.Entries);
}

internal static class DigestionCasStore
{
    internal const string RootPath = "Meta/Digestion/atoms/sha256/";

    internal static bool IsCanonicalPath(string path)
    {
        if (!path.StartsWith(RootPath, StringComparison.Ordinal)
            || path.Length != RootPath.Length + 64)
        {
            return false;
        }

        foreach (var value in path.AsSpan(RootPath.Length))
        {
            if (value is not (>= '0' and <= '9') and not (>= 'a' and <= 'f'))
            {
                return false;
            }
        }

        return true;
    }

    internal static DigestionCasObject Capture(ReadOnlySpan<byte> bytes)
    {
        var reference = "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes));
        return new DigestionCasObject(
            reference,
            RootPath + reference["sha256:".Length..],
            ImmutableArray.CreateRange(bytes.ToArray()));
    }

    internal static DigestionCasEvaluation EvaluateLedgerReferences(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot) =>
        EvaluateLedgerReferences(document, snapshot, changes: null);

    internal static DigestionCasEvaluation EvaluateLedgerReferences(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        RawChangeSet? changes,
        Func<string, bool>? isBaseFactAffected = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
        var findings = ImmutableArray.CreateBuilder<string>();
        var validAtomIds = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        foreach (var entry in document.RequireDigestionEntries())
        {
            var reference = entry.CasRef;
            if (!DigestionFingerprint.IsCanonicalSha256(reference))
            {
                findings.Add($"entry {entry.AtomId} cas_ref must use canonical sha256:<64 lowercase hex>");
                continue;
            }

            if (entry.Fingerprints.RawSha256 != reference)
            {
                findings.Add(
                    $"entry {entry.AtomId} cas_ref {reference} differs from raw fingerprint "
                    + entry.Fingerprints.RawSha256);
                continue;
            }

            // CAS bytes are content-addressed storage, not a query index.  A
            // status evaluation records the ledger reference and leaves blob
            // availability/hash verification to the command that explicitly
            // reads that atom (show/context/cover).  This keeps a frontier
            // query from traversing or rehashing the complete CAS store.
            validAtomIds.Add(entry.AtomId);
        }

        return new DigestionCasEvaluation(
            findings.Order(StringComparer.Ordinal).ToImmutableArray(),
            validAtomIds.ToImmutable(),
            changes?.Entries);
    }

    internal static bool EntryChanged(DigestionLedgerEntry entry, RawChangeSet changes)
    {
        if (changes.Paths.Any(static path => path.Value == BackfillInventoryLoader.RelativePath))
        {
            return true;
        }

        var sourcePrefix = BackfillInventoryLoader.RootPath + entry.SourceId + "/";
        var suffix = "/" + entry.AtomId + ".yaml";
        return changes.Paths.Any(path =>
            path.Value == sourcePrefix + "source.toml"
            || path.Value.StartsWith(sourcePrefix, StringComparison.Ordinal)
                && path.Value.EndsWith(suffix, StringComparison.Ordinal));
    }
}
