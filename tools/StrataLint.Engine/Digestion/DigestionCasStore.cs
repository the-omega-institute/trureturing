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
    int RehashedObjectCount,
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

    internal static DigestionCasEvaluation Evaluate(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot) =>
        Evaluate(document, snapshot, changes: null);

    internal static DigestionCasEvaluation Evaluate(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        RawChangeSet? changes,
        Func<string, bool>? isBaseFactAffected = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
        var findings = ImmutableArray.CreateBuilder<string>();
        var referencedPaths = new HashSet<string>(StringComparer.Ordinal);
        var validAtomIds = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var rehashedObjectCount = 0;
        foreach (var entry in document.RequireDigestionEntries())
        {
            var reference = entry.CasRef;
            var entryChanged = changes is null
                || EntryChanged(entry, changes)
                || isBaseFactAffected?.Invoke(entry.SourcePath) == true;
            if (!DigestionFingerprint.IsCanonicalSha256(reference))
            {
                if (entryChanged)
                {
                    findings.Add($"entry {entry.AtomId} cas_ref must use canonical sha256:<64 lowercase hex>");
                }
                continue;
            }

            var valid = true;
            if (entryChanged && entry.Fingerprints.RawSha256 != reference)
            {
                findings.Add(
                    $"entry {entry.AtomId} cas_ref {reference} differs from raw fingerprint "
                    + entry.Fingerprints.RawSha256);
                valid = false;
            }

            var path = RootPath + reference["sha256:".Length..];
            referencedPaths.Add(path);
            var blobChanged = changes is null
                || (isBaseFactAffected?.Invoke(path)
                    ?? changes.Paths.Any(changed => changed.Value == path));
            if (!entryChanged && !blobChanged)
            {
                validAtomIds.Add(entry.AtomId);
                continue;
            }

            if (!snapshot.TryGetFile(path, out var blob))
            {
                findings.Add($"entry {entry.AtomId} CAS blob is missing: {path}");
                continue;
            }

            if (blobChanged)
            {
                var actual = Capture(blob.RawBytes.AsSpan()).Reference;
                rehashedObjectCount++;
                if (actual != reference)
                {
                    findings.Add(
                        $"entry {entry.AtomId} CAS blob hash mismatch: {path} "
                        + $"declares {reference} but contains {actual}");
                    valid = false;
                }
            }

            if (valid)
            {
                validAtomIds.Add(entry.AtomId);
            }
        }

        var candidateCasPaths = snapshot.Files.Keys
            .Select(static path => path.Value)
            .Where(static path => path.StartsWith(RootPath, StringComparison.Ordinal));
        if (changes is not null)
        {
            var changedPaths = changes.Paths.Select(static path => path.Value).ToHashSet(StringComparer.Ordinal);
            candidateCasPaths = candidateCasPaths.Where(changedPaths.Contains);
        }

        foreach (var path in candidateCasPaths)
        {
            if (!referencedPaths.Contains(path))
            {
                findings.Add($"orphan CAS blob: {path}");
            }
        }

        return new DigestionCasEvaluation(
            findings.Order(StringComparer.Ordinal).ToImmutableArray(),
            validAtomIds.ToImmutable(),
            rehashedObjectCount,
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
