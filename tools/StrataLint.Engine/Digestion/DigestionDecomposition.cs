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
        TheoryAtomizer atomizer, TheoryAtomizerRules rules)
    {
        var frozen = DigestionAtom.FromFrozenCas(bytes);
        if (parent.CasRef != frozen.Fingerprints.RawSha256
            || parent.AtomId != frozen.Fingerprints.RawSha256[7..]
            || parent.Fingerprints != frozen.Fingerprints)
            throw new FormatException($"CAS_MISMATCH atom_id={parent.AtomId}");

        // Whole-source validators can require chapter context absent from frozen CAS.
        // Consume emitted plans where registered; other adapters use the same CAS grammar.
        ImmutableArray<DigestionClausePlan> plans = [];
        if (AtomizerRegistry.EmitsClausePlans(parent.Atomizer))
        {
            var document = atomizer(bytes.AsSpan(), rules);
            if (!document.UnregisteredGenres.IsEmpty)
                throw new FormatException("UNREGISTERED_GENRE " + string.Join(',', document.UnregisteredGenres));
            plans = document.ClausePlans;
        }
        foreach (var emitted in plans)
            RequireValid(emitted);
        var matching = plans.Where(p => p.Parent.Fingerprints == frozen.Fingerprints).ToArray();
        if (matching.Length > 1)
            throw new FormatException("AMBIGUOUS duplicate parent clause plans");
        var plan = matching.SingleOrDefault() ?? PlanClauses(frozen)
            ?? throw new FormatException("parent CAS blob has no clause plan (NO_CLAUSE_PLAN)");
        RequireValid(plan);
        return plan;
    }

    internal static DigestionClausePlan? PlanClauses(DigestionAtom parent)
    {
        if (!DigestionDecompositionPolicy.IsMultiClause(parent)) return null;
        var text = StrictUtf8.GetString(parent.RawBytes.AsSpan());
        var lines = Lines(text).ToArray();
        var bold = lines.Skip(1).Where(static line => line.Text.StartsWith("**", StringComparison.Ordinal)).ToArray();
        int[] boundaries;
        if (bold.Length > 0)
        {
            boundaries = [0, .. bold.Select(static line => line.Start)];
        }
        else
        {
            var items = lines.Where(static line => line.Text.StartsWith("- ", StringComparison.Ordinal)
                || line.Text.StartsWith("* ", StringComparison.Ordinal)).ToArray();
            if (items.Length < 2) return null;
            boundaries = [0, .. items.Skip(1).Select(static line => line.Start)];
        }

        // Persisted chains define the grammar: every span is a child, including
        // preamble, closing prose, and markers at any indentation or inside code.
        var segments = ImmutableArray.CreateBuilder<DigestionSegment>(boundaries.Length);
        for (var index = 0; index < boundaries.Length; index++)
        {
            var start = MarkdownAstAtomizer.ByteOffset(text, boundaries[index]);
            var end = index + 1 == boundaries.Length ? parent.RawBytes.Length
                : MarkdownAstAtomizer.ByteOffset(text, boundaries[index + 1]);
            var raw = parent.RawBytes[start..end];
            segments.Add(new DigestionSegment(DigestionSegmentKind.Claim, new DigestionAtom(
                parent.StartByte + start, parent.StartByte + end, raw,
                DigestionFingerprint.Compute(raw.AsSpan()), parent.Context,
                DigestionAtomStatusMarker.Parse(raw.AsSpan()))));
        }
        return new DigestionClausePlan(parent, segments.MoveToImmutable());
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
        DigestionClausePlan plan, IReadOnlyDictionary<string, DigestionLedgerEntry> globalEntries)
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
                id, child.Fingerprints, [], new DigestionReceipts([], [], [], null),
                new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open), captured.Reference));
        }
        var chain = ids.ToImmutable();
        if (!parent.Receipts.ChainAtoms.IsEmpty && !parent.Receipts.ChainAtoms.SequenceEqual(chain, StringComparer.Ordinal))
            throw new FormatException("CHAIN_CONFLICT existing chain differs from parent CAS plan");
        return new DigestionDecompositionWriteSet(parent with
        {
            Receipts = parent.Receipts with { ChainAtoms = chain, UnresolvedSubitems = [] },
        }, children.ToImmutable(), objects.ToImmutable());
    }

    private static void RequireValid(DigestionClausePlan plan)
    {
        if (IntegrityFailure(plan) is { } failure) throw new FormatException(failure);
    }

    private static IEnumerable<SourceLine> Lines(string text)
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

    private sealed record SourceLine(int Start, string Text);
}
