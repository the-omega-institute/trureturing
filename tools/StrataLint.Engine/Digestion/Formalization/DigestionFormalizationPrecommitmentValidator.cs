using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class DigestionFormalizationPrecommitmentValidator
{
    private readonly record struct CoverageEdge(
        string AtomId,
        string Gid,
        string RawSha256);

    internal static ImmutableArray<string> ValidateNewEdges(
        BackfillInventoryDocument baselineDocument,
        BackfillInventoryDocument candidateDocument,
        RepositorySnapshot baselineSnapshot,
        LeanAxiomReport candidateReport)
    {
        ArgumentNullException.ThrowIfNull(baselineDocument);
        ArgumentNullException.ThrowIfNull(candidateDocument);
        ArgumentNullException.ThrowIfNull(baselineSnapshot);
        ArgumentNullException.ThrowIfNull(candidateReport);

        var baselineEdges = new HashSet<CoverageEdge>();
        foreach (var entry in baselineDocument.RequireDigestionEntries())
        {
            foreach (var gid in entry.CoverageGids.Distinct(StringComparer.Ordinal))
            {
                if (TryCoverageEdge(entry, gid, out var edge))
                {
                    baselineEdges.Add(edge);
                }
            }
        }

        var findings = ImmutableArray.CreateBuilder<string>();
        foreach (var entry in candidateDocument.RequireDigestionEntries())
        {
            foreach (var gid in entry.CoverageGids.Distinct(StringComparer.Ordinal))
            {
                if (TryCoverageEdge(entry, gid, out var edge)
                    && baselineEdges.Contains(edge))
                {
                    continue;
                }

                try
                {
                    RequireBaseOwnedEdges(
                        baselineSnapshot,
                        DigestionFormalizationReceipt.PathForAtom(entry.AtomId),
                        entry,
                        [gid],
                        candidateReport);
                }
                catch (Exception exception) when (
                    exception is FormatException or InvalidOperationException)
                {
                    findings.Add(
                        $"coverage pair ({entry.AtomId}, {gid}) has no valid base-owned "
                        + $"formalization precommitment: {exception.Message}");
                }
            }
        }

        return findings.ToImmutable();
    }

    private static bool TryCoverageEdge(
        DigestionLedgerEntry entry,
        string gid,
        out CoverageEdge edge)
    {
        var receipts = entry.Receipts.Coverage
            .Where(receipt => string.Equals(receipt.Gid, gid, StringComparison.Ordinal))
            .ToArray();
        if (receipts.Length > 1)
        {
            edge = default;
            return false;
        }

        var rawSha256 = receipts.Length == 1
            ? receipts[0].SourceSha256
            : entry.Fingerprints.RawSha256;
        edge = new CoverageEdge(entry.AtomId, gid, rawSha256);
        return true;
    }

    internal static void RequireBaseOwnedEdges(
        RepositorySnapshot baselineSnapshot,
        string receiptPath,
        DigestionLedgerEntry entry,
        IEnumerable<string> gids,
        LeanAxiomReport candidateReport)
    {
        ArgumentNullException.ThrowIfNull(baselineSnapshot);
        ArgumentException.ThrowIfNullOrWhiteSpace(receiptPath);
        ArgumentNullException.ThrowIfNull(entry);
        ArgumentNullException.ThrowIfNull(gids);
        ArgumentNullException.ThrowIfNull(candidateReport);

        var receipt = LoadBaseOwnedReceipt(
            baselineSnapshot,
            receiptPath,
            entry.AtomId,
            entry.Fingerprints.RawSha256);
        foreach (var gidText in gids.Distinct(StringComparer.Ordinal))
        {
            RequireRegisteredSignature(receipt, entry.AtomId, gidText, candidateReport);
        }
    }

    internal static ImmutableHashSet<string> RegisteredBaseOwnedGids(
        RepositorySnapshot baselineSnapshot,
        string atomId,
        string rawSha256)
    {
        try
        {
            return LoadBaseOwnedReceipt(
                    baselineSnapshot,
                    DigestionFormalizationReceipt.PathForAtom(atomId),
                    atomId,
                    rawSha256)
                .RegisteredGids
                .ToImmutableHashSet(StringComparer.Ordinal);
        }
        catch (Exception exception) when (
            exception is FormatException or InvalidOperationException)
        {
            return ImmutableHashSet<string>.Empty;
        }
    }

    private static DigestionFormalizationReceipt LoadBaseOwnedReceipt(
        RepositorySnapshot baselineSnapshot,
        string receiptPath,
        string atomId,
        string rawSha256)
    {
        var receipt = DigestionFormalizationReceipt.LoadTrusted(baselineSnapshot, receiptPath);
        RequireEnvelopeBinding(receipt, atomId, rawSha256);
        return receipt;
    }

    private static void RequireEnvelopeBinding(
        DigestionFormalizationReceipt receipt,
        string atomId,
        string rawSha256)
    {
        if (!string.Equals(receipt.AtomId, atomId, StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                $"formalization receipt atom_id {receipt.AtomId} does not match atom {atomId}");
        }

        if (!string.Equals(receipt.CasRef, rawSha256, StringComparison.Ordinal)
            || !string.Equals(receipt.RawSha256, rawSha256, StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                $"formalization receipt fingerprint does not match atom {atomId} "
                + $"(atom raw {rawSha256})");
        }
    }

    private static void RequireRegisteredSignature(
        DigestionFormalizationReceipt receipt,
        string atomId,
        string gidText,
        LeanAxiomReport candidateReport)
    {
        if (!Gid.TryParse(gidText, out var gid))
        {
            throw new InvalidOperationException($"formalization receipt GID is invalid: {gidText}");
        }

        DigestionFormalizationSignature pinned;
        if (string.Equals(gidText, receipt.PrimaryGid, StringComparison.Ordinal))
        {
            pinned = receipt.Signature;
        }
        else
        {
            var matches = receipt.HostedExtensions
                .Where(extension => string.Equals(extension.Gid, gidText, StringComparison.Ordinal))
                .ToArray();
            if (matches.Length != 1)
            {
                throw new InvalidOperationException(
                    $"coverage edge ({atomId}, {gidText}) has no base-owned pre-committed signature");
            }

            pinned = matches[0].Signature;
        }

        var deposited = DigestionFormalizationReceipt.ResolveSignature(gid, candidateReport);
        if (deposited != pinned)
        {
            throw new InvalidOperationException(
                $"formalization declaration {gid.Value} signature "
                + $"({deposited.NameKey}, {deposited.Kind}, {deposited.Type}) "
                + "does not match the pre-committed signature "
                + $"({pinned.NameKey}, {pinned.Kind}, {pinned.Type})");
        }
    }
}
