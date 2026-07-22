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
    ImmutableArray<DigestionContext> Context);

internal sealed record DigestionSlice(bool IsClaim, ImmutableArray<byte> RawBytes);

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
        var text = StrictUtf8.GetString(rawBytes);
        if (text.StartsWith('\uFEFF'))
        {
            text = text[1..];
        }

        var normalized = text
            .Replace("\r\n", "\n", StringComparison.Ordinal)
            .Replace('\r', '\n')
            .Normalize(NormalizationForm.FormC);
        return new DigestionFingerprints(raw, Sha256(StrictUtf8.GetBytes(normalized)));
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

    private static string Sha256(ReadOnlySpan<byte> bytes) =>
        "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes));
}

internal static class GictAtomizer
{
    private static readonly Regex ClaimPattern = new(
        "^\\*\\*(?<kind>定理|定义|命题|引理|推论|观察|勘察|注)\\s*(?<number>[0-9]+\\.[0-9]+)",
        RegexOptions.CultureInvariant);
    private static readonly Regex UnknownNumberedClaimPattern = new(
        "^\\*\\*(?<kind>\\p{L}+)\\s*[0-9]+\\.[0-9]+",
        RegexOptions.CultureInvariant);
    private static readonly Regex AppendixClaimPattern = new(
        "^\\*\\*(?<number>E\\.[0-9]+)\\s+[^\\r\\n*]+\\*\\*",
        RegexOptions.CultureInvariant);
    private static readonly Regex LineagePattern = new(
        "^>\\s*\\*\\*谱系\\*\\*:",
        RegexOptions.CultureInvariant);
    private static readonly Regex HeartsPattern = new(
        "^\\*\\*心脏 O-5.*O-6",
        RegexOptions.CultureInvariant);

    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes) =>
        MarkdownAstAtomizer.Atomize(bytes, Identify, IdentifyConstant);

    private static string? Identify(string paragraph)
    {
        var match = ClaimPattern.Match(paragraph);
        if (match.Success)
        {
            return Kind(match.Groups["kind"].Value) + "/" + match.Groups["number"].Value;
        }

        var appendix = AppendixClaimPattern.Match(paragraph);
        if (appendix.Success)
        {
            return "appendix/" + appendix.Groups["number"].Value;
        }

        var unknown = UnknownNumberedClaimPattern.Match(paragraph);
        if (unknown.Success)
        {
            throw new TheorySourceFormatException(
                $"unknown GICT numbered claim kind {unknown.Groups["kind"].Value}");
        }

        if (HeartsPattern.IsMatch(paragraph))
        {
            return "open/O-5-O-6";
        }

        return LineagePattern.IsMatch(paragraph) ? "metadata/lineage" : null;
    }

    private static string Kind(string value) => value switch
    {
        "定理" => "theorem",
        "定义" => "definition",
        "命题" => "proposition",
        "引理" => "lemma",
        "推论" => "corollary",
        "观察" => "observation",
        "勘察" => "survey",
        "注" => "note",
        _ => throw new InvalidOperationException($"unknown GICT claim kind {value}"),
    };

    private static string? IdentifyConstant(string value) => value switch
    {
        "κ" => "constant/kappa",
        "C₀" => "constant/C0",
        "c*" => "constant/cstar",
        "h̄" => "constant/hbar",
        "s₁" => "constant/s1",
        "A_h" => "constant/Ah",
        "E" => "constant/E",
        "C_φ" => "constant/Cphi",
        "T₀" => "constant/T0",
        "δ̄" => "constant/delta-mean",
        "T₁" => "constant/T1",
        "B_h" => "constant/Bh",
        "c₁" => "constant/c1",
        "c₂" => "constant/c2",
        _ => null,
    };
}

internal static class PeriodicTreeAtomizer
{
    private static readonly Regex SectionHeadingPattern = new(
        "^(?<number>[0-9]+)\\.\\s+",
        RegexOptions.CultureInvariant);

    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes) =>
        MarkdownAstAtomizer.Atomize(bytes, static _ => null, identifyHeading: IdentifyHeading);

    private static string? IdentifyHeading(string heading)
    {
        var match = SectionHeadingPattern.Match(heading);
        return match.Success ? "section/" + match.Groups["number"].Value : null;
    }
}

internal static class PzgAtomizer
{
    private static readonly Regex ClaimPattern = new(
        "^\\*\\*(?<kind>前沿引注|定理形|定理|定义|命题|引理|推论|观察|评注|账目|条目|公理|范例|判据|后果|原则|规格|契约|延表|路线)\\s*(?<number>[0-9]+\\.[0-9]+[′″]*)",
        RegexOptions.CultureInvariant);
    private static readonly Regex TraceNotePattern = new(
        "^\\*\\*〔(?<number>[0-9]+\\.[0-9]+)\\s+追注",
        RegexOptions.CultureInvariant);
    private static readonly Regex UnknownNumberedClaimPattern = new(
        "^\\*\\*(?<kind>\\p{L}+)\\s*[0-9]+\\.[0-9]+",
        RegexOptions.CultureInvariant);
    private static readonly Regex OpenPattern = new(
        "^\\*\\*(?<id>O-[0-9]+)\\*\\*",
        RegexOptions.CultureInvariant);
    private static readonly Regex SupplementHeadingPattern = new(
        "^PZG_BEDC 增补册:第\\s*(?<version>[0-9]+)\\s*版",
        RegexOptions.CultureInvariant);
    private static readonly Regex RemarkHeadingPattern = new(
        "^评注\\s+(?<range>[0-9]+\\.[0-9]+(?:[–—-][0-9]+\\.[0-9]+)?)",
        RegexOptions.CultureInvariant);

    internal static AtomizedTheoryDocument Atomize(ReadOnlySpan<byte> bytes) =>
        MarkdownAstAtomizer.Atomize(bytes, Identify, identifyHeading: IdentifyHeading);

    private static string? Identify(string paragraph)
    {
        var match = ClaimPattern.Match(paragraph);
        if (match.Success)
        {
            return Kind(match.Groups["kind"].Value) + "/" + match.Groups["number"].Value;
        }

        var trace = TraceNotePattern.Match(paragraph);
        if (trace.Success)
        {
            return "trace-note/" + trace.Groups["number"].Value;
        }

        var open = OpenPattern.Match(paragraph);
        if (open.Success)
        {
            return "open/" + open.Groups["id"].Value;
        }

        var unknown = UnknownNumberedClaimPattern.Match(paragraph);
        if (unknown.Success)
        {
            throw new TheorySourceFormatException(
                $"unknown PZG numbered claim kind {unknown.Groups["kind"].Value}");
        }

        return null;
    }

    private static string? IdentifyHeading(string heading)
    {
        var supplement = SupplementHeadingPattern.Match(heading);
        if (supplement.Success)
        {
            return "metadata/supplement/" + supplement.Groups["version"].Value;
        }

        var remark = RemarkHeadingPattern.Match(heading);
        if (remark.Success)
        {
            return "remark/" + remark.Groups["range"].Value
                .Replace('–', '-')
                .Replace('—', '-');
        }

        if (heading.StartsWith("判负册", StringComparison.Ordinal))
        {
            return "negative-register/batch";
        }

        if (heading.StartsWith("候查清单", StringComparison.Ordinal))
        {
            return "research-queue/batch";
        }

        return heading.StartsWith("本批收束", StringComparison.Ordinal)
            ? "verdict/batch"
            : null;
    }

    private static string Kind(string value) => value switch
    {
        "定理" => "theorem",
        "定义" => "definition",
        "命题" => "proposition",
        "引理" => "lemma",
        "推论" => "corollary",
        "观察" => "observation",
        "评注" => "remark",
        "账目" => "ledger",
        "条目" => "entry",
        "公理" => "axiom",
        "范例" => "example",
        "判据" => "criterion",
        "后果" => "consequence",
        "原则" => "principle",
        "规格" => "specification",
        "契约" => "contract",
        "定理形" => "theorem-form",
        "前沿引注" => "frontier-note",
        "延表" => "extension-table",
        "路线" => "route",
        _ => throw new InvalidOperationException($"unknown PZG claim kind {value}"),
    };
}

internal static class MarkdownAstAtomizer
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static AtomizedTheoryDocument Atomize(
        ReadOnlySpan<byte> bytes,
        Func<string, string?> identify,
        Func<string, string?>? identifyFirstTableCell = null,
        Func<string, string?>? identifyHeading = null,
        Func<string, string?>? identifyFirstTableCellSource = null)
    {
        var raw = bytes.ToArray();
        var text = StrictUtf8.GetString(raw);
        var blocks = MarkdownBlockAst.Parse(text);
        var headings = new List<DigestionContext>();
        var candidates = new List<Candidate>();
        var headingStarts = new List<int>();
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
                        Extend: true));
                }

                headings.Add(new DigestionContext(heading.Level, heading.Text));
                headingStarts.Add(heading.Start);
                continue;
            }

            if (block is MarkdownTableRow row)
            {
                var tableAstPath = identifyFirstTableCellSource is not null
                    ? TheorySourceFormatException.IdentifyAt(
                        identifyFirstTableCellSource, row.FirstCellSourceText, row.Start, text)
                    : identifyFirstTableCell is not null
                    ? TheorySourceFormatException.IdentifyAt(
                        identifyFirstTableCell, row.FirstCellText, row.Start, text)
                    : TheorySourceFormatException.IdentifyAt(identify, row.Text, row.Start, text);
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
                    identify, line.Text, line.Start, text)))
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
                identify, paragraph.Text, paragraph.Start, text);
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
                candidate.Context));
            cursor = end;
        }

        if (cursor < raw.Length)
        {
            slices.Add(new DigestionSlice(false, ImmutableArray.CreateRange(raw[cursor..])));
        }

        return new AtomizedTheoryDocument(claims.MoveToImmutable(), slices.ToImmutable());
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
        bool Extend);

    private sealed record SourceLine(string Text, int Start, int End);
}

internal abstract record MarkdownBlock(int Start, int End);

internal sealed record MarkdownHeading(int Start, int End, int Level, string Text)
    : MarkdownBlock(Start, End);

internal sealed record MarkdownParagraph(int Start, int End, string Text)
    : MarkdownBlock(Start, End);

internal sealed record MarkdownTableRow(
    int Start, int End, string Text, string FirstCellText, string FirstCellSourceText)
    : MarkdownBlock(Start, End);

internal static class MarkdownBlockAst
{
    private static readonly Regex HeadingPattern = new(
        "^(?<marks>#{1,6})[ \\t]+(?<text>.*?)[ \\t]*#*[ \\t]*$",
        RegexOptions.CultureInvariant);
    private static readonly Regex TableDelimiterPattern = new(
        "^[ \\t]*\\|?[ \\t]*:?-{3,}:?[ \\t]*(?:\\|[ \\t]*:?-{3,}:?[ \\t]*)+\\|?[ \\t]*$",
        RegexOptions.CultureInvariant);

    internal static ImmutableArray<MarkdownBlock> Parse(string source)
    {
        var lines = ReadLines(source);
        var blocks = ImmutableArray.CreateBuilder<MarkdownBlock>();
        for (var index = 0; index < lines.Length;)
        {
            var line = lines[index];
            if (string.IsNullOrWhiteSpace(line.Text))
            {
                index++;
                continue;
            }

            var heading = HeadingPattern.Match(line.Text);
            if (heading.Success)
            {
                blocks.Add(new MarkdownHeading(
                    line.Start,
                    line.End,
                    heading.Groups["marks"].Length,
                    heading.Groups["text"].Value.Trim()));
                index++;
                continue;
            }

            if (IsFence(line.Text))
            {
                index = SkipFence(lines, index);
                continue;
            }

            if (index + 1 < lines.Length
                && line.Text.Contains('|')
                && TableDelimiterPattern.IsMatch(lines[index + 1].Text))
            {
                blocks.Add(TableRow(line));
                index += 2;
                while (index < lines.Length
                    && !string.IsNullOrWhiteSpace(lines[index].Text)
                    && lines[index].Text.Contains('|'))
                {
                    blocks.Add(TableRow(lines[index]));
                    index++;
                }

                continue;
            }

            var start = line.Start;
            var contentEnd = line.ContentEnd;
            var end = line.End;
            index++;
            while (index < lines.Length
                && !string.IsNullOrWhiteSpace(lines[index].Text)
                && !HeadingPattern.IsMatch(lines[index].Text)
                && !IsFence(lines[index].Text)
                && !(index + 1 < lines.Length
                    && lines[index].Text.Contains('|')
                    && TableDelimiterPattern.IsMatch(lines[index + 1].Text)))
            {
                contentEnd = lines[index].ContentEnd;
                end = lines[index].End;
                index++;
            }

            blocks.Add(new MarkdownParagraph(start, end, source[start..contentEnd]));
        }

        return blocks.ToImmutable();
    }

    private static MarkdownTableRow TableRow(MarkdownSourceLine line)
    {
        var firstCellSourceText = FirstCellSourceText(line.Text);
        return new(line.Start, line.End, line.Text, FirstCellPlainText(firstCellSourceText), firstCellSourceText);
    }

    private static string FirstCellSourceText(string row)
    {
        var value = row.Trim();
        if (value.StartsWith('|')) value = value[1..];
        var separator = value.IndexOf('|');
        if (separator >= 0) value = value[..separator];
        return value.Trim();
    }

    private static string FirstCellPlainText(string value)
    {
        while (value.Length >= 4
            && (value.StartsWith("**", StringComparison.Ordinal)
                && value.EndsWith("**", StringComparison.Ordinal)
                || value.StartsWith("__", StringComparison.Ordinal)
                && value.EndsWith("__", StringComparison.Ordinal)))
        {
            value = value[2..^2].Trim();
        }

        if (value.Length >= 2
            && value.StartsWith('`')
            && value.EndsWith('`'))
        {
            value = value[1..^1].Trim();
        }

        return value;
    }

    private static bool IsFence(string line)
    {
        var trimmed = line.TrimStart();
        return trimmed.StartsWith("```", StringComparison.Ordinal)
            || trimmed.StartsWith("~~~", StringComparison.Ordinal);
    }

    private static int SkipFence(ImmutableArray<MarkdownSourceLine> lines, int start)
    {
        var opening = lines[start].Text.TrimStart();
        var marker = opening.StartsWith("```", StringComparison.Ordinal) ? "```" : "~~~";
        for (var index = start + 1; index < lines.Length; index++)
        {
            if (lines[index].Text.TrimStart().StartsWith(marker, StringComparison.Ordinal))
            {
                return index + 1;
            }
        }

        return lines.Length;
    }

    private static ImmutableArray<MarkdownSourceLine> ReadLines(string source)
    {
        var lines = ImmutableArray.CreateBuilder<MarkdownSourceLine>();
        for (var start = 0; start < source.Length;)
        {
            var contentEnd = start;
            while (contentEnd < source.Length && source[contentEnd] is not ('\r' or '\n'))
            {
                contentEnd++;
            }

            var end = contentEnd;
            if (end < source.Length && source[end] == '\r') end++;
            if (end < source.Length && source[end] == '\n') end++;
            lines.Add(new MarkdownSourceLine(
                start,
                contentEnd,
                end,
                source[start..contentEnd]));
            start = end;
        }

        if (source.Length == 0)
        {
            return [];
        }

        return lines.ToImmutable();
    }

    private sealed record MarkdownSourceLine(int Start, int ContentEnd, int End, string Text);
}
