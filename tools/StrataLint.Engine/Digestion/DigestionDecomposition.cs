using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal enum DigestionSegmentKind { Claim, Structural }
internal sealed record DigestionSegment(DigestionSegmentKind Kind, DigestionAtom Atom);
internal sealed record DigestionDecompositionWriteSet(
    DigestionLedgerEntry Parent,
    ImmutableArray<DigestionLedgerEntry> NewEntries,
    ImmutableArray<DigestionCasObject> CasObjects);

internal static class DigestionDecomposition
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static DigestionClausePlan Plan(DigestionLedgerEntry parent, ImmutableArray<byte> bytes,
        TheoryAtomizer atomizer, RepositorySnapshot? snapshot = null,
        ImmutableArray<int> splitAt = default)
    {
        _ = AtomizerRegistry.Require(parent.Atomizer);
        var frozen = DigestionAtom.FromFrozenCas(bytes);
        if (parent.CasRef != frozen.Fingerprints.RawSha256
            || parent.AtomId != frozen.Fingerprints.RawSha256[7..]
            || parent.Fingerprints != frozen.Fingerprints)
            throw new FormatException($"CAS_MISMATCH atom_id={parent.AtomId}");

        // Stored direct children own history. Fresh grammar is never substituted for
        // an ordinary read of a materialized parent.
        if (!parent.Receipts.ChainAtoms.IsEmpty && snapshot is null)
            throw new FormatException("CHILD_CAS_MISSING stored chain requires its CAS snapshot");
        var persisted = PersistedPlan(parent, frozen, snapshot);
        if (persisted is not null)
        {
            RequireValid(persisted);
            if (splitAt.IsDefaultOrEmpty) return persisted;
        }

        var document = atomizer(bytes.AsSpan());
        var plans = document.ClausePlans;
        foreach (var emitted in plans)
            RequireValid(emitted);
        var matching = plans.Where(p => p.Parent.Fingerprints == frozen.Fingerprints).ToArray();
        if (matching.Length > 1)
            throw new FormatException("AMBIGUOUS duplicate parent clause plans");
        var canonical = matching.SingleOrDefault() ?? PlanClauses(frozen);
        var explicitPlan = splitAt.IsDefaultOrEmpty ? null : PlanAt(frozen, splitAt);
        if (canonical is not null && explicitPlan is not null
            && !canonical.Children.Select(static child => child.Fingerprints)
                .SequenceEqual(explicitPlan.Children.Select(static child => child.Fingerprints)))
            throw new FormatException("PLAN_CONFLICT split points differ from canonical clause plan");
        var plan = explicitPlan ?? persisted ?? canonical
            ?? throw new FormatException("parent CAS blob has no clause plan (NO_CLAUSE_PLAN)");
        RequireValid(plan);
        return plan;
    }

    private static DigestionClausePlan PlanAt(DigestionAtom parent, ImmutableArray<int> splitAt)
    {
        var segments = ImmutableArray.CreateBuilder<DigestionSegment>(splitAt.Length + 1);
        var start = 0;
        foreach (var end in splitAt.Add(parent.RawBytes.Length))
        {
            if (end <= start || end > parent.RawBytes.Length
                || end == parent.RawBytes.Length && segments.Count < splitAt.Length)
                throw new FormatException("SPLIT_AT_INVALID cuts must be strictly increasing interior byte offsets");
            var raw = parent.RawBytes[start..end];
            try { _ = StrictUtf8.GetCharCount(raw.AsSpan()); }
            catch (DecoderFallbackException)
            {
                throw new FormatException("SPLIT_AT_INVALID cut splits a UTF-8 character");
            }
            var child = DigestionAtom.FromFrozenCas(raw) with
            {
                StartByte = parent.StartByte + start,
                EndByte = parent.StartByte + end,
                Context = parent.Context,
            };
            segments.Add(new DigestionSegment(DigestionSegmentKind.Claim, child));
            start = end;
        }
        var plan = new DigestionClausePlan(parent, segments.MoveToImmutable()) { IsExplicit = true };
        RequireValid(plan);
        return plan;
    }

    private static DigestionClausePlan? PersistedPlan(DigestionLedgerEntry entry,
        DigestionAtom parent, RepositorySnapshot? snapshot)
    {
        if (entry.Receipts.ChainAtoms.IsEmpty || snapshot is null) return null;
        var segments = ImmutableArray.CreateBuilder<DigestionSegment>();
        var start = parent.StartByte;
        foreach (var childId in entry.Receipts.ChainAtoms)
        {
            if (!snapshot.TryGetFile(DigestionCasStore.RootPath + childId, out var blob))
                throw new FormatException($"CHILD_CAS_MISSING atom_id={childId}");
            try { _ = StrictUtf8.GetCharCount(blob.RawBytes.AsSpan()); }
            catch (DecoderFallbackException)
            {
                throw new FormatException($"CHILD_CAS_INVALID_UTF8 atom_id={childId}");
            }
            var child = DigestionAtom.FromFrozenCas(blob.RawBytes);
            if (child.Fingerprints.RawSha256 != "sha256:" + childId)
                throw new FormatException($"CHILD_CAS_MISMATCH atom_id={childId}");
            if (child.RawBytes.Length > parent.RawBytes.Length)
                throw new FormatException("clause plan children exceed parent bytes");
            // Stored children retain their unique raw positions, including structural
            // gaps that have no ledger identity. No current grammar chooses the chain.
            var offset = UniqueSubspanStart(parent.RawBytes.AsSpan(), child.RawBytes.AsSpan());
            if (offset < 0)
            {
                if (parent.RawBytes.AsSpan().IndexOf(child.RawBytes.AsSpan()) < 0)
                    throw new FormatException($"clause plan segment at byte {start} differs from its parent span");
                throw new FormatException("AMBIGUOUS clause plan child is not a unique parent sub-span");
            }
            var childStart = parent.StartByte + offset;
            if (childStart < start)
                throw new FormatException($"clause plan segment at byte {start} differs from its parent span");
            if (childStart > start)
                segments.Add(new DigestionSegment(DigestionSegmentKind.Structural,
                    Slice(parent, start - parent.StartByte, offset)));
            child = child with { StartByte = childStart, EndByte = childStart + child.RawBytes.Length, Context = parent.Context };
            segments.Add(new DigestionSegment(DigestionSegmentKind.Claim, child));
            start = child.EndByte;
        }
        if (entry.Receipts.ChainAtoms.Length < 2)
            throw new FormatException("clause plan has no proper claim decomposition");
        if (start < parent.EndByte)
            segments.Add(new DigestionSegment(DigestionSegmentKind.Structural,
                Slice(parent, start - parent.StartByte, parent.RawBytes.Length)));
        var gaps = segments.Where(static segment => segment.Kind == DigestionSegmentKind.Structural).ToArray();
        if (gaps.Length > 0)
        {
            // Only whole canonical structural spans may be absent from chain_atoms.
            // Truncated or omitted claims must not become structural by subtraction.
            var structural = PlanClauses(parent)?.Segments
                .Where(static segment => segment.Kind == DigestionSegmentKind.Structural).ToArray() ?? [];
            if (gaps.Any(gap => !structural.Any(segment =>
                segment.Atom.StartByte == gap.Atom.StartByte && segment.Atom.EndByte == gap.Atom.EndByte)))
                throw new FormatException("clause plan segments do not tile parent with structural gaps");
        }
        return new DigestionClausePlan(parent, segments.ToImmutable()) { IsExplicit = true };
    }

    internal static DigestionClausePlan? PlanClauses(DigestionAtom parent)
    {
        var text = StrictUtf8.GetString(parent.RawBytes.AsSpan());
        var document = GenericAtomizer.AtomizeStructure(parent.RawBytes.AsSpan());
        if (document.Claims.Length > 1)
        {
            var segments = ImmutableArray.CreateBuilder<DigestionSegment>();
            var cursor = 0;
            foreach (var atom in document.Claims)
            {
                if (atom.StartByte > cursor) Add(cursor, atom.StartByte, DigestionSegmentKind.Structural);
                Add(atom.StartByte, atom.EndByte, DigestionSegmentKind.Claim);
                cursor = atom.EndByte;
            }
            if (cursor < parent.RawBytes.Length) Add(cursor, parent.RawBytes.Length, DigestionSegmentKind.Structural);
            return new DigestionClausePlan(parent, segments.ToImmutable());

            void Add(int start, int end, DigestionSegmentKind kind) =>
                segments.Add(new DigestionSegment(kind, Slice(parent, start, end)));
        }

        var blocks = MarkdigBlockAst.ParseOwned(text);
        var bold = blocks.OfType<MarkdownParagraph>()
            .SelectMany(block => Lines(block.Text).Select(line => line with { Start = block.Start + line.Start }))
            .Where(line => IsIndependentBoldLead(line.Text))
            .Select(static line => line.Start).Where(static start => start > 0).ToArray();
        // Internal proof headings stay in the numbered claim's scope. Tables and
        // governed lists are opaque to paragraph-lead and list-item discovery.
        var boundaries = bold.Length > 0
            ? new[] { 0 }.Concat(bold).Distinct().Order().ToArray()
            : new[] { 0 }.Concat(MarkdigBlockAst.IndependentListStarts(text).Skip(1)).Distinct().Order().ToArray();
        if (boundaries.Length < 2) return null;
        return new DigestionClausePlan(parent, [.. boundaries.Select((start, index) =>
            new DigestionSegment(DigestionSegmentKind.Claim, Slice(parent,
                MarkdownAstAtomizer.ByteOffset(text, start),
                index + 1 == boundaries.Length ? parent.RawBytes.Length
                    : MarkdownAstAtomizer.ByteOffset(text, boundaries[index + 1]))))]);
    }

    private static bool IsIndependentBoldLead(string text)
    {
        if (!text.StartsWith("**", StringComparison.Ordinal)) return false;
        var close = text.IndexOf("**", 2, StringComparison.Ordinal);
        if (close <= 2) return false;
        var label = text[2..close].Trim();
        if (label.EndsWith(':') || label.EndsWith('：')
            || label.StartsWith("证明", StringComparison.Ordinal)
            || label.StartsWith("Proof", StringComparison.OrdinalIgnoreCase))
            return false;
        return !string.IsNullOrWhiteSpace(text[(close + 2)..]);
    }

    private static DigestionAtom Slice(DigestionAtom parent, int start, int end)
    {
        var raw = parent.RawBytes[start..end];
        return new DigestionAtom(parent.StartByte + start, parent.StartByte + end, raw,
            DigestionFingerprint.Compute(raw.AsSpan()), parent.Context,
            DigestionAtomStatusMarker.Parse(raw.AsSpan()));
    }

    internal static string? IntegrityFailure(DigestionClausePlan plan)
    {
        var parent = plan.Parent;
        if (parent.EndByte - parent.StartByte != parent.RawBytes.Length)
            return "clause plan parent range differs from its bytes";
        if (plan.Children.Length == 0 || plan.Segments.Length < 2)
            return "clause plan has no proper claim decomposition";
        var end = parent.StartByte;
        foreach (var segment in plan.Segments)
        {
            if (segment.Kind is not (DigestionSegmentKind.Claim or DigestionSegmentKind.Structural))
                return "clause plan has unknown segment kind";
            var atom = segment.Atom;
            if (atom.StartByte != end)
                return $"clause plan segments do not tile parent at byte {atom.StartByte}";
            if (atom.EndByte <= atom.StartByte || atom.EndByte > parent.EndByte
                || atom.StartByte < parent.StartByte || atom.RawBytes.Length >= parent.RawBytes.Length
                || atom.EndByte - atom.StartByte != atom.RawBytes.Length)
                return $"clause plan segment at byte {atom.StartByte} is outside its parent";
            var offset = atom.StartByte - parent.StartByte;
            if (!parent.RawBytes.AsSpan().Slice(offset, atom.RawBytes.Length).SequenceEqual(atom.RawBytes.AsSpan()))
                return $"clause plan segment at byte {atom.StartByte} differs from its parent span";
            if (segment.Kind == DigestionSegmentKind.Claim
                && UniqueSubspanStart(parent.RawBytes.AsSpan(), atom.RawBytes.AsSpan()) != offset)
                return $"AMBIGUOUS clause plan child at byte {atom.StartByte} is not a unique parent sub-span";
            if (atom.Fingerprints != DigestionFingerprint.Compute(atom.RawBytes.AsSpan()))
                return $"clause plan segment at byte {atom.StartByte} fingerprint does not match its raw bytes";
            end = atom.EndByte;
        }
        return end == parent.EndByte ? null : "clause plan segments do not tile parent at its end";
    }

    internal static DigestionDecompositionWriteSet Materialize(DigestionLedgerEntry parent,
        DigestionClausePlan plan, IReadOnlyDictionary<string, DigestionLedgerEntry> globalEntries,
        bool reconcileExistingChain = false, RepositorySnapshot? snapshot = null)
    {
        RequireValid(plan);
        if (parent.Fingerprints != plan.Parent.Fingerprints || parent.CasRef != plan.Parent.Fingerprints.RawSha256)
            throw new FormatException("CAS_MISMATCH clause plan parent");
        var children = ImmutableArray.CreateBuilder<DigestionLedgerEntry>();
        var objects = ImmutableArray.CreateBuilder<DigestionCasObject>();
        var ids = ImmutableArray.CreateBuilder<string>();
        foreach (var child in plan.Children)
        {
            var captured = DigestionCasStore.Capture(child.RawBytes.AsSpan());
            var id = captured.Reference[7..];
            ids.Add(id);
            if (globalEntries.TryGetValue(id, out var existing))
            {
                if (existing.CasRef != captured.Reference || existing.Fingerprints != child.Fingerprints)
                    throw new FormatException($"CHILD_IDENTITY_CONFLICT atom_id={id}");
                continue;
            }
            objects.Add(captured);
            children.Add(new DigestionLedgerEntry(parent.SourceId, parent.SourcePath, parent.Atomizer,
                id, child.Fingerprints, [], new DigestionReceipts([], [], null),
                new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open), captured.Reference));
        }
        var chain = ids.ToImmutable();
        if (reconcileExistingChain)
        {
            if (parent.Receipts.ChainAtoms.IsEmpty)
                throw new FormatException("CHAIN_RECONCILE_REQUIRES_EXISTING_CHAIN");
            if (!parent.Coverage.IsEmpty || !parent.Receipts.UnresolvedSubitems.IsEmpty
                || parent.Receipts.TailAuthorization is not null
                || parent.Receipts.Quarantine is not null
                || parent.Receipts.CoverDisposition is not null
                || parent.Receipts.Nonpropositional is not null)
                throw new FormatException("CHAIN_RECONCILE_LIVE_OBLIGATIONS");
            ArgumentNullException.ThrowIfNull(snapshot);
            // The old direct chain must itself be a lossless, identity-valid partition.
            // Reuse the same persisted-plan and nested-plan authority as ordinary decomposition.
            RequireValid(PersistedPlan(parent, plan.Parent, snapshot)!);
            _ = ValidatedClosure(parent.Receipts.ChainAtoms, globalEntries, snapshot);
            var retained = ValidatedClosure(chain.Where(globalEntries.ContainsKey), globalEntries, snapshot);
            retained.UnionWith(chain);
            foreach (var oldChild in parent.Receipts.ChainAtoms)
                if (!retained.Contains(oldChild))
                    throw new FormatException($"CHAIN_RECONCILE_DROPS_CHILD atom_id={oldChild}");
        }
        else if (!parent.Receipts.ChainAtoms.IsEmpty
            && !parent.Receipts.ChainAtoms.SequenceEqual(chain, StringComparer.Ordinal))
            throw new FormatException("CHAIN_CONFLICT existing chain differs from parent CAS plan");
        return new DigestionDecompositionWriteSet(parent with
        {
            Receipts = parent.Receipts with { ChainAtoms = chain, UnresolvedSubitems = [] },
        }, children.ToImmutable(), objects.ToImmutable());
    }

    internal static HashSet<string> ValidatedClosure(IEnumerable<string> roots,
        IReadOnlyDictionary<string, DigestionLedgerEntry> entries,
        RepositorySnapshot snapshot)
    {
        var seen = new HashSet<string>(StringComparer.Ordinal);
        var pending = new Stack<string>(roots);
        while (pending.TryPop(out var id))
        {
            if (!seen.Add(id)) continue;
            if (!entries.TryGetValue(id, out var entry))
                throw new FormatException($"CHILD_MISSING atom_id={id}");
            if (!snapshot.TryGetFile(DigestionCasStore.RootPath + id, out var blob))
                throw new FormatException($"CHILD_CAS_MISSING atom_id={id}");
            var fingerprint = DigestionFingerprint.Compute(blob.RawBytes.AsSpan());
            if (entry.AtomId != id || fingerprint.RawSha256 != "sha256:" + id
                || entry.CasRef != fingerprint.RawSha256 || entry.Fingerprints != fingerprint)
                throw new FormatException($"CHILD_IDENTITY_CONFLICT atom_id={id}");
            if (entry.Receipts.ChainAtoms.IsEmpty) continue;
            var nested = Plan(entry, blob.RawBytes, AtomizerRegistry.Require(entry.Atomizer).Atomize, snapshot);
            var materialized = Materialize(entry, nested, entries);
            if (!materialized.NewEntries.IsEmpty)
                throw new FormatException($"CHILD_MISSING parent={id}");
            foreach (var child in entry.Receipts.ChainAtoms) pending.Push(child);
        }
        return seen;
    }

    private static void RequireValid(DigestionClausePlan plan)
    {
        if (IntegrityFailure(plan) is { } failure) throw new FormatException(failure);
    }

    internal static IEnumerable<SourceLine> Lines(string text)
    {
        var start = 0;
        while (start < text.Length)
        {
            var end = text.IndexOfAny(['\r', '\n'], start);
            if (end < 0) end = text.Length;
            var line = text[start..end];
            if (!string.IsNullOrWhiteSpace(line))
                yield return new SourceLine(start + line.Length - line.TrimStart().Length, line.TrimStart());
            if (end < text.Length && text[end] == '\r') end++;
            if (end < text.Length && text[end] == '\n') end++;
            start = end;
        }
    }

    private static int UniqueSubspanStart(ReadOnlySpan<byte> parent, ReadOnlySpan<byte> child)
    {
        var start = parent.IndexOf(child);
        return child.IsEmpty || start < 0 || parent[(start + 1)..].IndexOf(child) >= 0 ? -1 : start;
    }

    internal sealed record SourceLine(int Start, string Text);
}
