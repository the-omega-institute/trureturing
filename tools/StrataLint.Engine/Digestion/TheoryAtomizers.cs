using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal sealed record DigestionFingerprints(string RawSha256, string NormalizedSha256);

internal sealed record DigestionContext(int Level, string Text);

internal sealed record DigestionAtom(
    string AstPath,
    int StartByte,
    int EndByte,
    ImmutableArray<byte> RawBytes,
    DigestionFingerprints Fingerprints,
    ImmutableArray<DigestionContext> Context,
    DigestionAtomStatusMarker StatusMarker)
{
    internal DigestionAtom(
        string astPath,
        int startByte,
        int endByte,
        ImmutableArray<byte> rawBytes,
        DigestionFingerprints fingerprints,
        ImmutableArray<DigestionContext> context)
        : this(astPath, startByte, endByte, rawBytes, fingerprints, context, DigestionAtomStatusMarker.Absent)
    {
    }

    internal static DigestionAtom FromFrozenCas(string astPath, ImmutableArray<byte> rawBytes) =>
        new(
            astPath,
            0,
            rawBytes.Length,
            rawBytes,
            DigestionFingerprint.Compute(rawBytes.AsSpan()),
            [],
            DigestionAtomStatusMarker.Parse(rawBytes.AsSpan()));
}

internal sealed record DigestionSlice(bool IsClaim, ImmutableArray<byte> RawBytes);

internal enum DigestionAtomStatusMarkerKind
{
    Absent,
    Valid,
    Malformed,
}

internal sealed record DigestionAtomStatusMarker(
    DigestionAtomStatusMarkerKind Kind,
    string? Status,
    string? Qualifier)
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    internal static readonly DigestionAtomStatusMarker Absent =
        new(DigestionAtomStatusMarkerKind.Absent, null, null);

    internal static DigestionAtomStatusMarker Parse(ReadOnlySpan<byte> atomBytes)
    {
        var atomText = StrictUtf8.GetString(atomBytes);
        if (!atomText.StartsWith("**", StringComparison.Ordinal))
        {
            return Absent;
        }

        var titleEnd = atomText.IndexOf("**", 2, StringComparison.Ordinal);
        if (titleEnd < 0)
        {
            return Absent;
        }

        var suffix = atomText.AsSpan(titleEnd + 2);
        var whitespaceLength = 0;
        while (whitespaceLength < suffix.Length && char.IsWhiteSpace(suffix[whitespaceLength]))
        {
            whitespaceLength++;
        }

        if (whitespaceLength >= suffix.Length || suffix[whitespaceLength] != '〔')
        {
            return Absent;
        }

        var markerStart = titleEnd + 3 + whitespaceLength;
        var markerEnd = atomText.IndexOf('〕', markerStart);
        var marker = markerEnd < 0 ? atomText[markerStart..] : atomText[markerStart..markerEnd];
        var namespaceMarker = marker.AsSpan().TrimStart();
        if (!namespaceMarker.StartsWith("closed", StringComparison.Ordinal)
            || (namespaceMarker.Length > "closed".Length
                && namespaceMarker["closed".Length] is not (';' or '；')
                && !char.IsWhiteSpace(namespaceMarker["closed".Length])))
        {
            return Absent;
        }

        var separator = marker.IndexOf(';', StringComparison.Ordinal);
        var status = separator < 0 ? marker : marker[..separator];
        var qualifier = separator < 0 ? null : marker[(separator + 1)..];
        var isPlainClosed = marker == "closed";
        var isQualifiedClosed = status == "closed"
            && separator == "closed".Length
            && marker.LastIndexOf(';') == separator
            && qualifier is not null
            && !string.IsNullOrWhiteSpace(qualifier);
        var kind = whitespaceLength == 0 && markerEnd >= 0 && (isPlainClosed || isQualifiedClosed)
            ? DigestionAtomStatusMarkerKind.Valid
            : DigestionAtomStatusMarkerKind.Malformed;
        return new DigestionAtomStatusMarker(kind, status, qualifier);
    }
}

internal sealed class AtomizedTheoryDocument
{
    internal AtomizedTheoryDocument(
        ImmutableArray<DigestionAtom> claims,
        ImmutableArray<DigestionSlice> slices)
    {
        Claims = claims;
        Slices = slices;
    }

    internal ImmutableArray<DigestionAtom> Claims { get; }

    internal ImmutableArray<DigestionSlice> Slices { get; }

    internal DigestionAtom ResolveClaim(string astPath)
    {
        var exact = Claims.Where(atom => atom.AstPath == astPath).ToArray();
        if (exact.Length == 1)
        {
            return exact[0];
        }

        var prefix = astPath + "/occurrence/";
        var qualified = Claims.Where(atom => atom.AstPath.StartsWith(prefix, StringComparison.Ordinal)).ToArray();
        return qualified.Length switch
        {
            1 => qualified[0],
            0 => throw new FormatException($"Markdown claim locator is absent: {astPath}"),
            _ => throw new FormatException($"ambiguous Markdown claim locator: {astPath}"),
        };
    }

    internal ImmutableArray<byte> Reassemble()
    {
        var length = Slices.Sum(static slice => slice.RawBytes.Length);
        var builder = ImmutableArray.CreateBuilder<byte>(length);
        foreach (var slice in Slices)
        {
            builder.AddRange(slice.RawBytes);
        }

        return builder.MoveToImmutable();
    }
}

internal static class DigestionFingerprint
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static DigestionFingerprints Compute(ReadOnlySpan<byte> rawBytes)
    {
        var raw = Sha256(rawBytes);
        var normalized = NormalizeText(rawBytes);
        return new DigestionFingerprints(raw, Sha256(StrictUtf8.GetBytes(normalized)));
    }

    internal static string NormalizeText(ReadOnlySpan<byte> rawBytes)
    {
        var text = StrictUtf8.GetString(rawBytes);
        if (text.StartsWith('\uFEFF'))
        {
            text = text[1..];
        }

        return text
            .Replace("\r\n", "\n", StringComparison.Ordinal)
            .Replace('\r', '\n')
            .Normalize(NormalizationForm.FormC);
    }

    internal static bool IsCanonicalSha256(string value) =>
        value.Length == 71
        && value.StartsWith("sha256:", StringComparison.Ordinal)
        && value.AsSpan(7).IndexOfAnyExcept("0123456789abcdef") < 0;

    internal static DigestionFingerprints ComputeOpaque(ReadOnlySpan<byte> rawBytes)
    {
        var raw = Sha256(rawBytes);
        return new DigestionFingerprints(raw, raw);
    }

    /// <summary>A short content address, for locators that have no readable text to slug.</summary>
    internal static string ShortHash(string value) =>
        Convert.ToHexStringLower(SHA256.HashData(StrictUtf8.GetBytes(value)))[..8];

    private static string Sha256(ReadOnlySpan<byte> bytes) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes));
}

/// <summary>The lead shape both numbered dialects share: <c>**&lt;genre&gt; &lt;number&gt;</c>.</summary>
internal sealed class NumberedClaims
{
    private static readonly Regex AnyNumberedLead = new(
        "^\\*\\*(?<kind>\\p{L}+)\\s*[0-9]+\\.[0-9]+",
        RegexOptions.CultureInvariant);

    private readonly string dialect;
    private readonly ImmutableArray<AtomizerMapping> genres;
    private readonly Regex registered;

    internal NumberedClaims(
        string dialect,
        ImmutableArray<AtomizerMapping> genres,
        string numberPattern)
    {
        this.dialect = dialect;
        this.genres = genres;
        registered = new Regex(
            "^\\*\\*(?<kind>"
            + string.Join('|', genres.Select(static item => Regex.Escape(item.Token)))
            + ")\\s*(?<number>" + numberPattern + ")",
            RegexOptions.CultureInvariant);
    }

    internal string? Identify(string paragraph)
    {
        var match = registered.Match(paragraph);
        return match.Success
            ? Kind(match.Groups["kind"].Value) + "/" + match.Groups["number"].Value
            : null;
    }

    /// <summary>Fails closed on a lead that is numbered but names no registered genre.</summary>
    internal void RejectUnregistered(string paragraph)
    {
        var unknown = AnyNumberedLead.Match(paragraph);
        if (unknown.Success)
        {
            throw new TheorySourceFormatException(
                $"unknown {dialect} numbered claim kind {unknown.Groups["kind"].Value}");
        }
    }

    private string Kind(string value) =>
        genres.FirstOrDefault(item => item.Token == value)?.Value
        ?? throw new InvalidOperationException($"unknown {dialect} claim kind {value}");
}

internal static class GictAtomizer
{
    private const string NumberPattern = "[0-9]+\\.[0-9]+";
    private static readonly Regex AppendixClaimPattern = new(
        "^\\*\\*(?<number>E\\.[0-9]+)\\s+[^\\r\\n*]+\\*\\*",
        RegexOptions.CultureInvariant);

    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes, TheoryAtomizerRules rules) =>
        MarkdownAstAtomizer.Atomize(
            bytes,
            paragraph => Identify(paragraph, rules),
            value => IdentifyConstant(value, rules));

    private static string? Identify(string paragraph, TheoryAtomizerRules rules)
    {
        var claims = new NumberedClaims("GICT", rules.GictGenres, NumberPattern);
        if (claims.Identify(paragraph) is { } locator)
        {
            return locator;
        }

        var appendix = AppendixClaimPattern.Match(paragraph);
        if (appendix.Success)
        {
            return "appendix/" + appendix.Groups["number"].Value;
        }

        claims.RejectUnregistered(paragraph);

        return rules.GictClaimPrefixes
            .FirstOrDefault(item => paragraph.StartsWith(item.Token, StringComparison.Ordinal))
            ?.Value;
    }

    private static string? IdentifyConstant(string value, TheoryAtomizerRules rules) =>
        rules.GictConstants.FirstOrDefault(item => item.Token == value)?.Value;

}

internal static class PeriodicTreeAtomizer
{
    private static readonly Regex SectionHeadingPattern = new(
        "^(?<number>[0-9]+)\\.\\s+",
        RegexOptions.CultureInvariant);

    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes, TheoryAtomizerRules _) =>
        MarkdownAstAtomizer.Atomize(bytes, static _ => null, identifyHeading: IdentifyHeading);

    private static string? IdentifyHeading(string heading)
    {
        var match = SectionHeadingPattern.Match(heading);
        return match.Success ? "section/" + match.Groups["number"].Value : null;
    }
}

internal static class PzgAtomizer
{
    private const string NumberPattern = "[0-9]+\\.[0-9]+(?:\\.[0-9]+)?[′″]*";
    private static readonly Regex OpenPattern = new(
        "^\\*\\*(?<id>O-[0-9]+)\\*\\*",
        RegexOptions.CultureInvariant);

    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes, TheoryAtomizerRules rules) =>
        MarkdownAstAtomizer.Atomize(
            bytes,
            paragraph => Identify(paragraph, rules),
            identifyHeading: heading => IdentifyHeading(heading, rules));

    private static string? Identify(string paragraph, TheoryAtomizerRules rules)
    {
        var claims = new NumberedClaims("PZG", rules.PzgGenres, NumberPattern);
        if (claims.Identify(paragraph) is { } locator)
        {
            return locator;
        }

        var trace = Regex.Match(
            paragraph,
            "^\\*\\*〔(?<number>[0-9]+\\.[0-9]+)\\s+"
                + Regex.Escape(rules.PzgMarkers["trace-note"]),
            RegexOptions.CultureInvariant);
        if (trace.Success)
        {
            return "trace-note/" + trace.Groups["number"].Value;
        }

        var open = OpenPattern.Match(paragraph);
        if (open.Success)
        {
            return "open/" + open.Groups["id"].Value;
        }

        claims.RejectUnregistered(paragraph);

        return null;
    }

    private static string? IdentifyHeading(string heading, TheoryAtomizerRules rules)
    {
        var supplementPrefix = rules.PzgHeadingPrefixes
            .Single(item => item.Value == "metadata/supplement").Token;
        var supplement = Regex.Match(
            heading,
            "^" + Regex.Escape(supplementPrefix) + "\\s*(?<version>[0-9]+)\\s*版",
            RegexOptions.CultureInvariant);
        if (supplement.Success)
        {
            return "metadata/supplement/" + supplement.Groups["version"].Value;
        }

        var remark = rules.PzgGenres
            .Where(static item => item.Value == "remark")
            .Select(item => Regex.Match(
                heading,
                "^" + Regex.Escape(item.Token)
                    + "\\s+(?<range>[0-9]+\\.[0-9]+(?:[–—-][0-9]+\\.[0-9]+)?)",
                RegexOptions.CultureInvariant))
            .FirstOrDefault(static match => match.Success);
        if (remark is { Success: true })
        {
            return "remark/" + remark.Groups["range"].Value
                .Replace('–', '-')
                .Replace('—', '-');
        }

        return rules.PzgHeadingPrefixes
            .Where(static item => item.Value != "metadata/supplement")
            .FirstOrDefault(item => heading.StartsWith(item.Token, StringComparison.Ordinal))?.Value;
    }
}

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
        Func<string, string?>? identifyFirstTableCell = null,
        Func<string, string?>? identifyHeading = null,
        Func<string, string?>? identifyFirstTableCellSource = null,
        Func<string, ImmutableArray<MarkdownBlock>>? parse = null,
        Func<MarkdownTableRow, string?>? identifyTableRow = null,
        bool dropEmptyHeadingClaims = false)
    {
        var raw = bytes.ToArray();
        var text = StrictUtf8.GetString(raw);
        var blocks = (parse ?? MarkdownBlockAst.Parse)(text);
        var headings = new List<DigestionContext>();
        var candidates = new List<Candidate>();
        var headingStarts = new List<int>();
        var failures = new List<UnrecognisedLead>();
        foreach (var block in blocks)
        {
            if (block is MarkdownHeading heading)
            {
                while (headings.Count > 0 && headings[^1].Level >= heading.Level)
                {
                    headings.RemoveAt(headings.Count - 1);
                }

                var headingAstPath = identifyHeading?.Invoke(heading.Text);
                if (headingAstPath is not null)
                {
                    candidates.Add(new Candidate(
                        headingAstPath,
                        heading.Start,
                        text.Length,
                        headings.ToImmutableArray(),
                        Extend: true,
                        IsHeading: true));
                }

                headings.Add(new DigestionContext(heading.Level, heading.Text));
                headingStarts.Add(heading.Start);
                continue;
            }

            if (block is MarkdownTableRow row)
            {
                var tableAstPath = identifyTableRow is not null
                    ? identifyTableRow(row)
                    : identifyFirstTableCellSource is not null
                    ? TheorySourceFormatException.IdentifyAt(
                        identifyFirstTableCellSource, row.FirstCellSourceText, row.Start, text, failures)
                    : identifyFirstTableCell is not null
                    ? TheorySourceFormatException.IdentifyAt(
                        identifyFirstTableCell, row.FirstCellText, row.Start, text, failures)
                    : TheorySourceFormatException.IdentifyAt(identify, row.Text, row.Start, text, failures);
                if (tableAstPath is not null)
                {
                    candidates.Add(new Candidate(
                        tableAstPath,
                        row.Start,
                        row.End,
                        headings.ToImmutableArray(),
                        Extend: false));
                }

                continue;
            }

            if (block is not MarkdownParagraph paragraph)
            {
                continue;
            }

            var lineClaims = SourceLines(paragraph.Text, paragraph.Start)
                .Select(line => (Line: line, AstPath: TheorySourceFormatException.IdentifyAt(
                    identify, line.Text, line.Start, text, failures)))
                .Where(static item => item.AstPath is not null)
                .ToArray();
            if (lineClaims.Length > 1)
            {
                foreach (var lineClaim in lineClaims)
                {
                    candidates.Add(new Candidate(
                        lineClaim.AstPath!,
                        lineClaim.Line.Start,
                        lineClaim.Line.End,
                        headings.ToImmutableArray(),
                        Extend: false));
                }

                continue;
            }

            var astPath = TheorySourceFormatException.IdentifyAt(
                identify, paragraph.Text, paragraph.Start, text, failures);
            if (astPath is null)
            {
                continue;
            }

            candidates.Add(new Candidate(
                astPath,
                paragraph.Start,
                text.Length,
                headings.ToImmutableArray(),
                Extend: true));
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
            .Concat(headingStarts)
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

            var nestedBoundary = boundaries.FirstOrDefault(start =>
                start > candidate.StartCharacter && start < candidate.EndCharacter);
            if (nestedBoundary > 0)
            {
                candidates[index] = candidate with { EndCharacter = nestedBoundary };
            }
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
        var locatorCounts = candidates
            .GroupBy(static candidate => candidate.AstPath, StringComparer.Ordinal)
            .ToDictionary(static group => group.Key, static group => group.Count(), StringComparer.Ordinal);
        var locatorOccurrences = new Dictionary<string, int>(StringComparer.Ordinal);
        var cursor = 0;
        foreach (var candidate in candidates.OrderBy(static item => item.StartCharacter))
        {
            locatorOccurrences.TryGetValue(candidate.AstPath, out var occurrence);
            occurrence++;
            locatorOccurrences[candidate.AstPath] = occurrence;
            var astPath = locatorCounts[candidate.AstPath] == 1
                ? candidate.AstPath
                : $"{candidate.AstPath}/occurrence/{occurrence}";
            var start = ByteOffset(text, candidate.StartCharacter);
            var end = ByteOffset(text, candidate.EndCharacter);
            if (start < cursor || end <= start || end > raw.Length)
            {
                throw new FormatException($"invalid Markdown AST span for {astPath}");
            }

            if (start > cursor)
            {
                slices.Add(new DigestionSlice(false, ImmutableArray.CreateRange(raw[cursor..start])));
            }

            var atomBytes = ImmutableArray.CreateRange(raw[start..end]);
            slices.Add(new DigestionSlice(true, atomBytes));
            claims.Add(new DigestionAtom(
                astPath,
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

        return new AtomizedTheoryDocument(claims.MoveToImmutable(), slices.ToImmutable());
    }

    private static bool IsHeadingOnly(string text, Candidate candidate)
    {
        var slice = text.AsSpan(
            candidate.StartCharacter,
            candidate.EndCharacter - candidate.StartCharacter);
        var lineEnd = slice.IndexOfAny('\r', '\n');
        return lineEnd >= 0 && slice[lineEnd..].IsWhiteSpace();
    }

    private static int ByteOffset(string text, int characterOffset) =>
        characterOffset == text.Length
            ? StrictUtf8.GetByteCount(text)
            : StrictUtf8.GetByteCount(text.AsSpan(0, characterOffset));

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
        string AstPath,
        int StartCharacter,
        int EndCharacter,
        ImmutableArray<DigestionContext> Context,
        bool Extend,
        bool IsHeading = false);

    private sealed record SourceLine(string Text, int Start, int End);
}
