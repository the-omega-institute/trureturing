using System.Collections.Immutable;
using System.Security.Cryptography;

namespace StrataLint.Engine;

internal sealed record DigestionCasObject(
    string Reference,
    string RelativePath,
    ImmutableArray<byte> Bytes);

internal sealed record DigestionCasEvaluation(
    ImmutableArray<string> Findings,
    ImmutableHashSet<string> ValidAtomIds);

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

    internal static ImmutableArray<string> ValidateAppendOnly(
        RepositorySnapshot current,
        RepositorySnapshot baseline)
    {
        ArgumentNullException.ThrowIfNull(current);
        ArgumentNullException.ThrowIfNull(baseline);
        var findings = ImmutableArray.CreateBuilder<string>();
        foreach (var (path, baselineBlob) in baseline.Files
                     .Where(static item => IsCanonicalPath(item.Key.Value))
                     .OrderBy(static item => item.Key.Value, StringComparer.Ordinal))
        {
            if (!current.Files.TryGetValue(path, out var currentBlob))
            {
                findings.Add($"baseline CAS blob was deleted: {path.Value}");
            }
            else if (!currentBlob.RawBytes.AsSpan().SequenceEqual(baselineBlob.RawBytes.AsSpan()))
            {
                findings.Add($"baseline CAS blob was rewritten: {path.Value}");
            }
        }

        return findings.ToImmutable();
    }

    internal static DigestionCasEvaluation Evaluate(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
        var findings = ImmutableArray.CreateBuilder<string>();
        var referencedPaths = new HashSet<string>(StringComparer.Ordinal);
        var validAtomIds = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        foreach (var entry in document.RequireDigestionEntries())
        {
            var reference = entry.CasRef;
            if (!DigestionFingerprint.IsCanonicalSha256(reference))
            {
                findings.Add($"entry {entry.AtomId} cas_ref must use canonical sha256:<64 lowercase hex>");
                continue;
            }

            var valid = true;
            if (entry.Fingerprints.RawSha256 != reference)
            {
                findings.Add(
                    $"entry {entry.AtomId} cas_ref {reference} differs from raw fingerprint "
                    + entry.Fingerprints.RawSha256);
                valid = false;
            }

            var path = RootPath + reference["sha256:".Length..];
            referencedPaths.Add(path);
            if (!snapshot.TryGetFile(path, out var blob))
            {
                findings.Add($"entry {entry.AtomId} CAS blob is missing: {path}");
                continue;
            }

            var actual = Capture(blob.RawBytes.AsSpan()).Reference;
            if (actual != reference)
            {
                findings.Add(
                    $"entry {entry.AtomId} CAS blob hash mismatch: {path} "
                    + $"declares {reference} but contains {actual}");
                valid = false;
            }

            if (valid)
            {
                validAtomIds.Add(entry.AtomId);
            }
        }

        foreach (var path in snapshot.Files.Keys
                     .Select(static path => path.Value)
                     .Where(static path => path.StartsWith(RootPath, StringComparison.Ordinal)))
        {
            if (!referencedPaths.Contains(path))
            {
                findings.Add($"orphan CAS blob: {path}");
            }
        }

        return new DigestionCasEvaluation(
            findings.Order(StringComparer.Ordinal).ToImmutableArray(),
            validAtomIds.ToImmutable());
    }
}
