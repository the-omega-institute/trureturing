using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class DigestionLedgerAligner
{
    private static bool ClausePlanInputsChanged(
        DigestionLedgerSource source,
        RawChangeSet? changes)
    {
        if (changes is null)
        {
            return true;
        }

        if (changes.Paths.Any(path =>
                path.Value == source.SourcePath
                || path.Value == TheoryAtomizerDataLoader.DataPath
                || IsAtomizerImplementationPath(path.Value)
                || path.Value == BackfillInventoryLoader.RelativePath
                || path.Value == $"{BackfillInventoryLoader.RootPath}{source.SourceId}/source.toml"))
        {
            return true;
        }

        foreach (var entry in source.Entries)
        {
            if (DigestionCasStore.EntryChanged(entry, changes)
                || DigestionFingerprint.IsCanonicalSha256(entry.CasRef)
                    && changes.Paths.Any(path => path.Value ==
                        DigestionCasStore.RootPath + entry.CasRef["sha256:".Length..]))
            {
                return true;
            }
        }

        return false;
    }

    private static string? ClausePlanIntegrityFailure(AtomizedTheoryDocument document)
    {
        var parentPaths = new HashSet<string>(StringComparer.Ordinal);
        foreach (var plan in document.ClausePlans)
        {
            if (!parentPaths.Add(plan.ParentAstPath))
            {
                return $"duplicate clause plan parent {plan.ParentAstPath}";
            }

            var parents = document.Claims
                .Where(atom => atom.AstPath == plan.ParentAstPath)
                .ToArray();
            if (parents.Length != 1)
            {
                return $"clause plan parent {plan.ParentAstPath} resolves to {parents.Length} claims";
            }

            if (plan.Children.Length < 2)
            {
                return $"clause plan parent {plan.ParentAstPath} has fewer than two children";
            }

            var parent = parents[0];
            var childPaths = new HashSet<string>(StringComparer.Ordinal);
            var previousEnd = parent.StartByte;
            foreach (var child in plan.Children)
            {
                if (!childPaths.Add(child.AstPath)
                    || !child.AstPath.StartsWith(parent.AstPath + "/clause/", StringComparison.Ordinal))
                {
                    return $"clause plan parent {plan.ParentAstPath} has an invalid child ast_path";
                }

                if (child.StartByte < parent.StartByte
                    || child.EndByte > parent.EndByte
                    || child.EndByte <= child.StartByte
                    || child.RawBytes.Length >= parent.RawBytes.Length
                    || child.EndByte - child.StartByte != child.RawBytes.Length)
                {
                    return $"clause plan child {child.AstPath} is outside its parent";
                }

                if (child.StartByte != previousEnd)
                {
                    return $"clause plan children do not tile parent {plan.ParentAstPath} at {child.AstPath}";
                }

                var relativeStart = child.StartByte - parent.StartByte;
                if (!parent.RawBytes.AsSpan()[relativeStart..(relativeStart + child.RawBytes.Length)]
                        .SequenceEqual(child.RawBytes.AsSpan()))
                {
                    return $"clause plan child {child.AstPath} differs from its parent span";
                }

                if (UniqueSubspanStart(parent.RawBytes.AsSpan(), child.RawBytes.AsSpan()) != relativeStart)
                {
                    return $"clause plan child {child.AstPath} is not a unique parent sub-span";
                }

                if (child.Fingerprints != DigestionFingerprint.Compute(child.RawBytes.AsSpan()))
                {
                    return $"clause plan child {child.AstPath} fingerprint does not match its raw bytes";
                }

                previousEnd = child.EndByte;
            }

            if (previousEnd != parent.EndByte)
            {
                return $"clause plan children do not tile parent {plan.ParentAstPath} at its end";
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
                entry.AstPath == plannedParent.AstPath
                && FingerprintsMatch(entry.Fingerprints, plannedParent.Fingerprints))
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
                + $"recomputed source span {plannedParent.AstPath}";
    }

    private static void AlignNestedChildren(
        DigestionLedgerSource source,
        ImmutableArray<DigestionClausePlan> clausePlans,
        IReadOnlyDictionary<string, DigestionAtom> claims,
        IReadOnlySet<string> validAtomIds,
        RepositorySnapshot snapshot,
        IDictionary<string, DigestionReceiptAlignment> alignments,
        IDictionary<string, DigestionAtom> matchedAtoms,
        ISet<string> clausePlanChainParents,
        ISet<string> verifiedClausePlanParents,
        ICollection<string> findings)
    {
        var byId = source.Entries.ToDictionary(static entry => entry.AtomId, StringComparer.Ordinal);
        var plansByParent = clausePlans.ToDictionary(static plan => plan.ParentAstPath, StringComparer.Ordinal);
        var plannedChildPaths = clausePlans
            .SelectMany(static plan => plan.Children)
            .Select(static child => child.AstPath)
            .ToHashSet(StringComparer.Ordinal);
        foreach (var plannedEntry in source.Entries.Where(entry => plannedChildPaths.Contains(entry.AstPath)))
        {
            alignments[plannedEntry.AtomId] = DigestionReceiptAlignment.Rejected;
            matchedAtoms.Remove(plannedEntry.AtomId);
        }

        foreach (var parent in source.Entries.Where(static entry => entry.Receipts.ChainAtoms.Length > 0))
        {
            var claimedByPlan = plansByParent.ContainsKey(parent.AstPath)
                || parent.Receipts.ChainAtoms.Any(childId =>
                    byId.TryGetValue(childId, out var child)
                    && plannedChildPaths.Contains(child.AstPath));
            if (!claimedByPlan)
            {
                continue;
            }

            clausePlanChainParents.Add(parent.AtomId);
            foreach (var childId in parent.Receipts.ChainAtoms)
            {
                if (byId.ContainsKey(childId))
                {
                    alignments[childId] = DigestionReceiptAlignment.Rejected;
                    matchedAtoms.Remove(childId);
                }
            }

            if (!validAtomIds.Contains(parent.AtomId))
            {
                RejectClauseChain(parent, "parent CAS proof is invalid", findings);
                continue;
            }

            if (!alignments.TryGetValue(parent.AtomId, out var parentAlignment)
                || parentAlignment != DigestionReceiptAlignment.Seen)
            {
                RejectClauseChain(parent, "parent is not structurally aligned", findings);
                continue;
            }

            if (!plansByParent.TryGetValue(parent.AstPath, out var plan))
            {
                RejectClauseChain(parent, $"no recomputed plan exists for {parent.AstPath}", findings);
                continue;
            }

            var parentPath = DigestionCasStore.RootPath + parent.CasRef["sha256:".Length..];
            if (!snapshot.TryGetFile(parentPath, out var parentBlob)
                || !parentBlob.RawBytes.AsSpan().SequenceEqual(
                    claims[plan.ParentAstPath].RawBytes.AsSpan()))
            {
                RejectClauseChain(parent, "parent CAS bytes differ from recomputed plan source span", findings);
                continue;
            }

            if (plan.Children.Length < 2)
            {
                RejectClauseChain(parent, "recomputed plan has fewer than two children", findings);
                continue;
            }

            if (parent.Receipts.ChainAtoms.Length != plan.Children.Length)
            {
                RejectClauseChain(
                    parent,
                    $"chain cardinality {parent.Receipts.ChainAtoms.Length} does not match recomputed plan "
                    + $"cardinality {plan.Children.Length}",
                    findings);
                continue;
            }

            if (parent.Receipts.ChainAtoms.Distinct(StringComparer.Ordinal).Count()
                != parent.Receipts.ChainAtoms.Length)
            {
                RejectClauseChain(parent, "chain contains duplicate child atom_ids", findings);
                continue;
            }

            var plannedChildren = plan.Children.ToDictionary(static child => child.AstPath, StringComparer.Ordinal);
            var accepted = new List<(string AtomId, DigestionLedgerEntry Entry, RepositoryFile Blob)>();
            string? rejectionReason = null;
            foreach (var childId in parent.Receipts.ChainAtoms)
            {
                if (!byId.TryGetValue(childId, out var child))
                {
                    rejectionReason = $"listed child {childId} is absent from source {source.SourceId}";
                    break;
                }

                if (!validAtomIds.Contains(childId))
                {
                    rejectionReason = $"listed child {childId} has invalid CAS proof";
                    break;
                }

                if (!plannedChildren.Remove(child.AstPath, out var plannedChild))
                {
                    rejectionReason = $"listed child {childId} ast_path {child.AstPath} "
                        + "is not an unclaimed recomputed plan member";
                    break;
                }

                if (child.Fingerprints != plannedChild.Fingerprints)
                {
                    rejectionReason = $"listed child {childId} fingerprint differs from recomputed plan member "
                        + plannedChild.AstPath;
                    break;
                }

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

                accepted.Add((childId, child, childBlob));
            }

            if (rejectionReason is not null)
            {
                RejectClauseChain(parent, rejectionReason, findings);
                continue;
            }

            if (plannedChildren.Count != 0)
            {
                RejectClauseChain(
                    parent,
                    "chain does not cover recomputed plan members: "
                    + string.Join(", ", plannedChildren.Keys.Order(StringComparer.Ordinal)),
                    findings);
                continue;
            }

            foreach (var child in accepted)
            {
                alignments[child.AtomId] = DigestionReceiptAlignment.Seen;
                matchedAtoms[child.AtomId] = DigestionAtom.FromFrozenCas(
                    child.Entry.AstPath,
                    child.Blob.RawBytes);
            }

            verifiedClausePlanParents.Add(parent.AtomId);
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
