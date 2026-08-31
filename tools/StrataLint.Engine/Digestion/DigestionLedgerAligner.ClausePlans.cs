using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class DigestionLedgerAligner
{
    private static string? ClausePlanIntegrityFailure(AtomizedTheoryDocument document)
    {
        var parents = new HashSet<(int Start, int End, string Hash)>();
        foreach (var plan in document.ClausePlans)
        {
            var parentKey = (plan.Parent.StartByte, plan.Parent.EndByte, plan.Parent.Fingerprints.RawSha256);
            if (!parents.Add(parentKey))
            {
                return $"duplicate clause plan parent at byte {plan.Parent.StartByte}";
            }

            if (!document.Claims.Contains(plan.Parent))
            {
                return $"clause plan parent at byte {plan.Parent.StartByte} is not a top-level atom";
            }

            if (plan.Children.Length < 2)
            {
                return $"clause plan parent at byte {plan.Parent.StartByte} has fewer than two children";
            }

            var parent = plan.Parent;
            var previousEnd = parent.StartByte;
            foreach (var child in plan.Children)
            {
                if (child.StartByte < parent.StartByte
                    || child.EndByte > parent.EndByte
                    || child.EndByte <= child.StartByte
                    || child.RawBytes.Length >= parent.RawBytes.Length
                    || child.EndByte - child.StartByte != child.RawBytes.Length)
                {
                    return $"clause plan child at byte {child.StartByte} is outside its parent";
                }

                if (child.StartByte != previousEnd)
                {
                    return $"clause plan children do not tile parent at byte {child.StartByte}";
                }

                var relativeStart = child.StartByte - parent.StartByte;
                if (!parent.RawBytes.AsSpan()[relativeStart..(relativeStart + child.RawBytes.Length)]
                        .SequenceEqual(child.RawBytes.AsSpan()))
                {
                    return $"clause plan child at byte {child.StartByte} differs from its parent span";
                }

                if (UniqueSubspanStart(parent.RawBytes.AsSpan(), child.RawBytes.AsSpan()) != relativeStart)
                {
                    return $"clause plan child at byte {child.StartByte} is not a unique parent sub-span";
                }

                if (child.Fingerprints != DigestionFingerprint.Compute(child.RawBytes.AsSpan()))
                {
                    return $"clause plan child at byte {child.StartByte} fingerprint does not match its raw bytes";
                }

                previousEnd = child.EndByte;
            }

            if (previousEnd != parent.EndByte)
            {
                return $"clause plan children do not tile parent at byte {parent.StartByte} at its end";
            }
        }

        return null;
    }

    private static string? ClausePlanCasAuthorityFailure(
        DigestionLedgerSource source,
        DigestionAtom plannedParent,
        IReadOnlySet<string> validAtomIds,
        RepositorySnapshot snapshot)
    {
        var ledgerParents = source.Entries.Where(entry =>
                FingerprintsMatch(entry.Fingerprints, plannedParent.Fingerprints))
            .ToArray();
        if (ledgerParents.Length != 1)
        {
            return null;
        }

        var ledgerParent = ledgerParents[0];
        if (!validAtomIds.Contains(ledgerParent.AtomId))
        {
            return $"entry {ledgerParent.AtomId} clause plan parent CAS proof is invalid";
        }

        var parentPath = DigestionCasStore.RootPath + ledgerParent.CasRef["sha256:".Length..];
        if (!snapshot.TryGetFile(parentPath, out var parentBlob))
        {
            return $"entry {ledgerParent.AtomId} clause plan parent CAS blob is missing: {parentPath}";
        }

        return parentBlob.RawBytes.AsSpan().SequenceEqual(plannedParent.RawBytes.AsSpan())
            ? null
            : $"entry {ledgerParent.AtomId} clause plan parent CAS bytes differ from "
                + $"recomputed source span at byte {plannedParent.StartByte}";
    }

    private static void AlignNestedChildren(
        DigestionLedgerSource source,
        ImmutableArray<DigestionClausePlan> currentClausePlans,
        IReadOnlySet<string> validAtomIds,
        IReadOnlyDictionary<string, DigestionLedgerEntry> candidateEntriesById,
        RepositorySnapshot snapshot,
        IDictionary<string, DigestionReceiptAlignment> alignments,
        IDictionary<string, DigestionAtom> matchedAtoms,
        ISet<string> clausePlanChainParents,
        ISet<string> verifiedClausePlanParents,
        ISet<string> verifiedClausePlanMembers,
        ICollection<string> findings)
    {
        var byId = source.Entries.ToDictionary(static entry => entry.AtomId, StringComparer.Ordinal);
        RejectCurrentFrontierClausePlanMembers(
            source,
            currentClausePlans,
            alignments,
            matchedAtoms,
            verifiedClausePlanMembers);

        foreach (var parent in source.Entries.Where(static entry => entry.Receipts.ChainAtoms.Length > 0))
        {
            if (!validAtomIds.Contains(parent.AtomId))
            {
                ClaimClausePlanChain(
                    parent,
                    byId,
                    alignments,
                    matchedAtoms,
                    clausePlanChainParents);
                RejectClauseChain(parent, "parent CAS proof is invalid", findings);
                continue;
            }

            var parentPath = DigestionCasStore.RootPath + parent.CasRef["sha256:".Length..];
            if (!snapshot.TryGetFile(parentPath, out var parentBlob))
            {
                ClaimClausePlanChain(
                    parent,
                    byId,
                    alignments,
                    matchedAtoms,
                    clausePlanChainParents);
                RejectClauseChain(parent, $"parent CAS blob is missing: {parentPath}", findings);
                continue;
            }

            var frozenParent = DigestionAtom.FromFrozenCas(parentBlob.RawBytes);
            var plan = PzgAtomizer.PlanClauses(frozenParent);
            ClaimClausePlanChain(
                parent,
                byId,
                alignments,
                matchedAtoms,
                clausePlanChainParents);
            if (plan is null)
            {
                RejectClauseChain(parent, "parent CAS blob has no clause plan", findings);
                continue;
            }

            if (parent.Receipts.ChainAtoms.Length != plan.Children.Length)
            {
                RejectClauseChain(
                    parent,
                    $"chain cardinality {parent.Receipts.ChainAtoms.Length} does not match parent CAS plan "
                    + $"cardinality {plan.Children.Length}",
                    findings);
                continue;
            }

            var accepted = new List<(string AtomId, DigestionLedgerEntry Entry, RepositoryFile Blob)>();
            string? rejectionReason = null;
            for (var index = 0; index < parent.Receipts.ChainAtoms.Length; index++)
            {
                var childId = parent.Receipts.ChainAtoms[index];
                if (!byId.TryGetValue(childId, out var child)
                    && !candidateEntriesById.TryGetValue(childId, out child))
                {
                    rejectionReason = $"listed child {childId} is absent from every source (globally missing)";
                    break;
                }

                if (!validAtomIds.Contains(childId))
                {
                    rejectionReason = $"listed child {childId} has invalid CAS proof";
                    break;
                }

                var plannedChild = plan.Children[index];
                var childPath = DigestionCasStore.RootPath + child.CasRef["sha256:".Length..];
                if (!snapshot.TryGetFile(childPath, out var childBlob))
                {
                    rejectionReason = $"listed child {childId} CAS blob is missing: {childPath}";
                    break;
                }

                if (child.Fingerprints != DigestionFingerprint.Compute(childBlob.RawBytes.AsSpan()))
                {
                    rejectionReason = $"listed child {childId} CAS bytes disagree with its fingerprints";
                    break;
                }

                if (!childBlob.RawBytes.AsSpan().SequenceEqual(plannedChild.RawBytes.AsSpan()))
                {
                    rejectionReason = $"listed child {childId} bytes differ from parent CAS plan member "
                        + $"at position {index + 1}";
                    break;
                }

                accepted.Add((childId, child, childBlob));
            }

            if (rejectionReason is not null)
            {
                RejectClauseChain(parent, rejectionReason, findings);
                continue;
            }

            foreach (var child in accepted)
            {
                verifiedClausePlanMembers.Add(child.AtomId);
                alignments[child.AtomId] = DigestionReceiptAlignment.Seen;
                matchedAtoms[child.AtomId] = DigestionAtom.FromFrozenCas(child.Blob.RawBytes);
            }

            verifiedClausePlanParents.Add(parent.AtomId);
        }
    }

    private static void RejectCurrentFrontierClausePlanMembers(
        DigestionLedgerSource source,
        ImmutableArray<DigestionClausePlan> currentClausePlans,
        IDictionary<string, DigestionReceiptAlignment> alignments,
        IDictionary<string, DigestionAtom> matchedAtoms,
        ISet<string> verifiedClausePlanMembers)
    {
        var plannedChildIds = currentClausePlans
            .SelectMany(static plan => plan.Children)
            .Select(static child => child.Fingerprints.RawSha256["sha256:".Length..])
            .ToHashSet(StringComparer.Ordinal);
        // A verified parent-CAS chain claim is stronger than a current-frontier rejection.
        foreach (var plannedEntry in source.Entries.Where(entry =>
                     plannedChildIds.Contains(entry.AtomId)
                     && !verifiedClausePlanMembers.Contains(entry.AtomId)))
        {
            alignments[plannedEntry.AtomId] = DigestionReceiptAlignment.Rejected;
            matchedAtoms.Remove(plannedEntry.AtomId);
        }
    }

    private static void ClaimClausePlanChain(
        DigestionLedgerEntry parent,
        IReadOnlyDictionary<string, DigestionLedgerEntry> entriesById,
        IDictionary<string, DigestionReceiptAlignment> alignments,
        IDictionary<string, DigestionAtom> matchedAtoms,
        ISet<string> clausePlanChainParents)
    {
        clausePlanChainParents.Add(parent.AtomId);
        foreach (var childId in parent.Receipts.ChainAtoms)
        {
            if (!entriesById.ContainsKey(childId))
            {
                continue;
            }

            alignments[childId] = DigestionReceiptAlignment.Rejected;
            matchedAtoms.Remove(childId);
        }
    }

    private static void RejectClauseChain(
        DigestionLedgerEntry parent,
        string reason,
        ICollection<string> findings) =>
        findings.Add($"entry {parent.AtomId} malformed clause chain: {reason}");

    private static int UniqueSubspanStart(ReadOnlySpan<byte> parent, ReadOnlySpan<byte> child)
    {
        if (child.IsEmpty)
        {
            return -1;
        }

        var start = parent.IndexOf(child);
        if (start < 0 || parent[(start + 1)..].IndexOf(child) >= 0)
        {
            return -1;
        }

        return start;
    }
}
