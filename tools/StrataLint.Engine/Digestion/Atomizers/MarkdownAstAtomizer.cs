using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static class MarkdownAstAtomizer
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    /// <summary>
    /// <paramref name="parse"/> selects the block AST. It defaults to the line scanner
    /// because the registered dialects' receipts are content-addressed over the boundaries
    /// that scanner produces; only the default atomizer, which has no receipts to preserve,
    /// passes a different one.
    /// </summary>
    internal static AtomizedTheoryDocument Atomize(
        ReadOnlySpan<byte> bytes,
        Func<string, string?> identify,
        Func<GenreRegistryCheck> genreRegistryCheck,
        Func<string, string?>? identifyFirstTableCell = null,
        Func<string, string?>? identifyHeading = null,
        Func<string, string?>? identifyFirstTableCellSource = null,
        Func<string, ImmutableArray<MarkdownBlock>>? parse = null,
        Func<MarkdownTableRow, string?>? identifyTableRow = null,
        bool dropEmptyHeadingClaims = false,
        bool extendLineClaims = true,
        Func<string, bool>? identifyHeadingClaim = null)
    {
        ArgumentNullException.ThrowIfNull(genreRegistryCheck);
        var raw = bytes.ToArray();
        var text = StrictUtf8.GetString(raw);
        var blocks = (parse ?? MarkdownBlockAst.Parse)(text);
        var headings = new List<DigestionContext>();
        var candidates = new List<Candidate>();
        var headingStarts = new List<HeadingBoundary>();
        var failures = new List<UnrecognisedLead>();
        foreach (var block in blocks)
        {
            if (block is MarkdownHeading heading)
            {
                while (headings.Count > 0 && headings[^1].Level >= heading.Level)
                {
                    headings.RemoveAt(headings.Count - 1);
                }

                var headingTag = identifyHeading?.Invoke(heading.Text);
                if (headingTag is not null)
                {
                    candidates.Add(new Candidate(
                        heading.Start,
                        text.Length,
                        headings.ToImmutableArray(),
                        Extend: true,
                        IsClaim: identifyHeadingClaim?.Invoke(heading.Text) ?? false,
                        ScopeHeadingLevel: heading.Level,
                        IsHeading: true));
                }

                headings.Add(new DigestionContext(heading.Level, heading.Text));
                headingStarts.Add(new HeadingBoundary(heading.Start, heading.Level));
                continue;
            }

            if (block is MarkdownTableRow row)
            {
                var tableTag = identifyTableRow is not null
                    ? identifyTableRow(row)
                    : identifyFirstTableCellSource is not null
                    ? TheorySourceFormatException.IdentifyAt(
                        identifyFirstTableCellSource, row.FirstCellSourceText, row.Start, text, failures)
                    : identifyFirstTableCell is not null
                    ? TheorySourceFormatException.IdentifyAt(
                        identifyFirstTableCell, row.FirstCellText, row.Start, text, failures)
                    : TheorySourceFormatException.IdentifyAt(identify, row.Text, row.Start, text, failures);
                if (tableTag is not null)
                {
                    candidates.Add(new Candidate(
                        row.Start,
                        row.End,
                        headings.ToImmutableArray(),
                        Extend: false,
                        IsClaim: true,
                        ScopeHeadingLevel: ScopeHeadingLevel(headings)));
                }

                continue;
            }

            if (block is not MarkdownParagraph paragraph)
            {
                continue;
            }

            var lineClaims = SourceLines(paragraph.Text, paragraph.Start)
                .Select(line => (Line: line, Tag: TheorySourceFormatException.IdentifyAt(
                    identify, line.Text, line.Start, text, failures)))
                .Where(static item => item.Tag is not null)
                .ToArray();
            if (lineClaims.Length > 1)
            {
                foreach (var lineClaim in lineClaims)
                {
                    candidates.Add(new Candidate(
                        lineClaim.Line.Start,
                        extendLineClaims ? text.Length : lineClaim.Line.End,
                        headings.ToImmutableArray(),
                        Extend: extendLineClaims,
                        IsClaim: true,
                        ScopeHeadingLevel: ScopeHeadingLevel(headings)));
                }

                continue;
            }

            var tag = TheorySourceFormatException.IdentifyAt(
                identify, paragraph.Text, paragraph.Start, text, failures);
            if (tag is null)
            {
                continue;
            }

            candidates.Add(new Candidate(
                paragraph.Start,
                text.Length,
                headings.ToImmutableArray(),
                Extend: true,
                IsClaim: true,
                ScopeHeadingLevel: ScopeHeadingLevel(headings)));
        }

        if (failures.Count > 0)
        {
            // Grouped by cause because one unknown lead is reported many times: once per
            // source line, once again as the whole paragraph, and once per repetition in
            // the volume. Naming each cause once, with its first line and how often it
            // occurs, is what a reader needs to register the dialect in a single pass.
            throw new TheorySourceFormatException(
                TheorySourceFormatException.Summarise(failures));
        }

        var boundaries = candidates.Select(static candidate => candidate.StartCharacter)
            .Concat(headingStarts.Select(static heading => heading.StartCharacter))
            .Distinct()
            .Order()
            .ToArray();
        for (var index = 0; index < candidates.Count; index++)
        {
            var candidate = candidates[index];
            if (!candidate.Extend)
            {
                continue;
            }

            var nestedBoundary = identifyHeadingClaim is not null && candidate.IsClaim
                ? FirstScopedClaimBoundary(candidate, candidates, headingStarts)
                : boundaries.FirstOrDefault(start =>
                    start > candidate.StartCharacter && start < candidate.EndCharacter);
            if (nestedBoundary > 0)
            {
                candidates[index] = candidate with { EndCharacter = nestedBoundary };
            }
        }

        if (identifyHeadingClaim is not null)
        {
            var claimSpans = candidates.Where(static candidate => candidate.IsClaim).ToArray();
            candidates.RemoveAll(candidate =>
                !candidate.IsClaim && claimSpans.Any(claim =>
                    claim.StartCharacter < candidate.StartCharacter
                    && candidate.StartCharacter < claim.EndCharacter));
        }

        if (dropEmptyHeadingClaims)
        {
            // A heading whose whole body was claimed by finer atoms is left holding only its
            // own line. That atom states nothing, so it could never be discharged and would
            // sit open forever; the heading itself is not lost, because every atom beneath it
            // carries it in its context.
            candidates.RemoveAll(candidate =>
                candidate.IsHeading && IsHeadingOnly(text, candidate));
        }

        var claims = ImmutableArray.CreateBuilder<DigestionAtom>(candidates.Count);
        var slices = ImmutableArray.CreateBuilder<DigestionSlice>(candidates.Count * 2 + 1);
        var cursor = 0;
        foreach (var candidate in candidates.OrderBy(static item => item.StartCharacter))
        {
            var start = ByteOffset(text, candidate.StartCharacter);
            var end = ByteOffset(text, candidate.EndCharacter);
            if (start < cursor || end <= start || end > raw.Length)
            {
                throw new FormatException($"invalid Markdown AST span at byte {start}");
            }

            if (start > cursor)
            {
                slices.Add(new DigestionSlice(false, ImmutableArray.CreateRange(raw[cursor..start])));
            }

            var atomBytes = ImmutableArray.CreateRange(raw[start..end]);
            slices.Add(new DigestionSlice(true, atomBytes));
            claims.Add(new DigestionAtom(
                start,
                end,
                atomBytes,
                DigestionFingerprint.Compute(atomBytes.AsSpan()),
                candidate.Context,
                DigestionAtomStatusMarker.Parse(atomBytes.AsSpan())));
            cursor = end;
        }

        if (cursor < raw.Length)
        {
            slices.Add(new DigestionSlice(false, ImmutableArray.CreateRange(raw[cursor..])));
        }

        return new AtomizedTheoryDocument(
            claims.MoveToImmutable(),
            slices.ToImmutable(),
            genreRegistryCheck());
    }

    private static bool IsHeadingOnly(string text, Candidate candidate)
    {
        var slice = text.AsSpan(
            candidate.StartCharacter,
            candidate.EndCharacter - candidate.StartCharacter);
        var lineEnd = slice.IndexOfAny('\r', '\n');
        return lineEnd >= 0 && slice[lineEnd..].IsWhiteSpace();
    }

    internal static int ByteOffset(string text, int characterOffset) =>
        characterOffset == text.Length
            ? StrictUtf8.GetByteCount(text)
            : StrictUtf8.GetByteCount(text.AsSpan(0, characterOffset));

    private static int? ScopeHeadingLevel(List<DigestionContext> headings) =>
        headings.Count == 0 ? null : headings[^1].Level;

    private static int FirstScopedClaimBoundary(
        Candidate candidate,
        List<Candidate> candidates,
        List<HeadingBoundary> headingStarts)
    {
        var nextClaim = candidates
            .Where(item => item.IsClaim && item.StartCharacter > candidate.StartCharacter)
            .Select(static item => item.StartCharacter)
            .DefaultIfEmpty(int.MaxValue)
            .Min();
        var nextPeerHeading = headingStarts
            .Where(heading =>
                heading.StartCharacter > candidate.StartCharacter
                && (candidate.ScopeHeadingLevel is null
                    || heading.Level <= candidate.ScopeHeadingLevel.Value))
            .Select(static heading => heading.StartCharacter)
            .DefaultIfEmpty(int.MaxValue)
            .Min();
        var boundary = Math.Min(nextClaim, nextPeerHeading);
        return boundary < candidate.EndCharacter ? boundary : 0;
    }

    private static IEnumerable<SourceLine> SourceLines(string paragraph, int sourceStart)
    {
        var offset = 0;
        while (offset < paragraph.Length)
        {
            var lineEnd = paragraph.IndexOfAny(['\r', '\n'], offset);
            if (lineEnd < 0) lineEnd = paragraph.Length;
            var next = lineEnd;
            while (next < paragraph.Length && paragraph[next] is '\r' or '\n') next++;
            yield return new SourceLine(
                paragraph[offset..lineEnd],
                sourceStart + offset,
                sourceStart + next);
            offset = next;
        }
    }

    private sealed record Candidate(
        int StartCharacter,
        int EndCharacter,
        ImmutableArray<DigestionContext> Context,
        bool Extend,
        bool IsClaim,
        int? ScopeHeadingLevel,
        bool IsHeading = false);

    private sealed record SourceLine(string Text, int Start, int End);

    private sealed record HeadingBoundary(int StartCharacter, int Level);
}
