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
        DigestionLedgerSource? baselineSource,
        ImmutableArray<DigestionClausePlan> currentClausePlans,
        IReadOnlySet<string> validAtomIds,
        RepositorySnapshot snapshot,
        IDictionary<string, DigestionReceiptAlignment> alignments,
        IDictionary<string, DigestionAtom> matchedAtoms,
        ISet<string> clausePlanChainParents,
        ISet<string> verifiedClausePlanParents,
        ICollection<string> findings)
    {
        var byId = source.Entries.ToDictionary(static entry => entry.AtomId, StringComparer.Ordinal);
        var inheritedChainChildren = InheritedChainChildren(source, baselineSource);
        RejectCurrentFrontierClausePlanMembers(
            source,
            currentClausePlans,
            inheritedChainChildren,
            alignments,
            matchedAtoms);

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

            var frozenParent = DigestionAtom.FromFrozenCas(parent.AstPath, parentBlob.RawBytes);
            var plan = PzgAtomizer.PlanClauses(frozenParent);
            if (plan is null && source.Atomizer == AtomizerRegistry.ObserverId)
            {
                continue;
            }

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

            if (parent.Receipts.ChainAtoms.Distinct(StringComparer.Ordinal).Count()
                != parent.Receipts.ChainAtoms.Length)
            {
                RejectClauseChain(parent, "chain contains duplicate child atom_ids", findings);
                continue;
            }

            var accepted = new List<(string AtomId, DigestionLedgerEntry Entry, RepositoryFile Blob)>();
            string? rejectionReason = null;
            for (var index = 0; index < parent.Receipts.ChainAtoms.Length; index++)
            {
                var childId = parent.Receipts.ChainAtoms[index];
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

                var plannedChild = plan.Children[index];
                if (child.AstPath != plannedChild.AstPath)
                {
                    rejectionReason = $"listed child {childId} chain order differs from parent CAS plan "
                        + $"at position {index + 1}: ast_path {child.AstPath}, expected {plannedChild.AstPath}";
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

                if (!childBlob.RawBytes.AsSpan().SequenceEqual(plannedChild.RawBytes.AsSpan()))
                {
                    rejectionReason = $"listed child {childId} bytes differ from parent CAS plan member "
                        + plannedChild.AstPath;
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
                alignments[child.AtomId] = DigestionReceiptAlignment.Seen;
                matchedAtoms[child.AtomId] = DigestionAtom.FromFrozenCas(
                    child.Entry.AstPath,
                    child.Blob.RawBytes);
            }

            verifiedClausePlanParents.Add(parent.AtomId);
        }
    }

    private static void RejectCurrentFrontierClausePlanMembers(
        DigestionLedgerSource source,
        ImmutableArray<DigestionClausePlan> currentClausePlans,
        IReadOnlySet<string> inheritedChainChildren,
        IDictionary<string, DigestionReceiptAlignment> alignments,
        IDictionary<string, DigestionAtom> matchedAtoms)
    {
        var plannedChildPaths = currentClausePlans
            .SelectMany(static plan => plan.Children)
            .Select(static child => child.AstPath)
            .ToHashSet(StringComparer.Ordinal);
        foreach (var plannedEntry in source.Entries.Where(entry =>
                     plannedChildPaths.Contains(entry.AstPath)
                     && !inheritedChainChildren.Contains(entry.AtomId)))
        {
            alignments[plannedEntry.AtomId] = DigestionReceiptAlignment.Rejected;
            matchedAtoms.Remove(plannedEntry.AtomId);
        }
    }

    private static HashSet<string> InheritedChainChildren(
        DigestionLedgerSource source,
        DigestionLedgerSource? baselineSource)
    {
        if (baselineSource is null)
        {
            return [];
        }

        var candidateById = source.Entries.ToDictionary(
            static entry => entry.AtomId,
            StringComparer.Ordinal);
        var baselineById = baselineSource.Entries.ToDictionary(
            static entry => entry.AtomId,
            StringComparer.Ordinal);
        return baselineSource.Entries
            .SelectMany(static parent => parent.Receipts.ChainAtoms)
            .Where(childId =>
                candidateById.TryGetValue(childId, out var candidateChild)
                && baselineById.TryGetValue(childId, out var baselineChild)
                && CanonicalEntry(source, candidateChild)
                    == CanonicalEntry(baselineSource, baselineChild))
            .ToHashSet(StringComparer.Ordinal);
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
