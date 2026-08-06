using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static class ConeAtomizer
{
    private static readonly Regex NumberedClaimPattern = new(
        "^\\*\\*(?<genre>\\p{L}+)\\s+(?<number>[0-9]+\\.[0-9]+[′″]*)",
        RegexOptions.CultureInvariant);
    private static readonly Regex ChapterHeadingPattern = new(
        "^第(?<number>十一|十|〇|一|二|三|四|五|六|七|八|九)章(?:\\s|$)",
        RegexOptions.CultureInvariant);

    internal static AtomizedTheoryDocument Atomize(
        ReadOnlySpan<byte> bytes,
        TheoryAtomizerRules rules)
    {
        ArgumentNullException.ThrowIfNull(rules);
        var document = MarkdownAstAtomizer.Atomize(
            bytes,
            paragraph => Identify(paragraph, rules));
        if (document.Claims.Any(static atom =>
                atom.AstPath.Contains("/occurrence/", StringComparison.Ordinal)))
        {
            throw new TheorySourceFormatException("duplicate cone claim locator");
        }

        foreach (var atom in document.Claims)
        {
            ValidateChapter(atom);
        }

        return document;
    }

    private static string? Identify(string paragraph, TheoryAtomizerRules rules)
    {
        var match = NumberedClaimPattern.Match(paragraph);
        if (match.Success)
        {
            var genre = match.Groups["genre"].Value;
            var mapping = rules.ConeClaimPrefixes.FirstOrDefault(item =>
                item.Token.Split('|').Contains(genre, StringComparer.Ordinal));
            if (mapping is null)
            {
                throw Unknown(paragraph);
            }

            var titleEnd = paragraph.IndexOf("**", 2, StringComparison.Ordinal);
            if (titleEnd < 0 || paragraph[titleEnd - 1] != '。')
            {
                throw Unknown(paragraph);
            }

            var templates = mapping.Value.Split('|');
            var exactProofGrade = paragraph.AsSpan(0, titleEnd)
                .EndsWith("[证]。", StringComparison.Ordinal);
            var template = exactProofGrade && templates.Length == 2
                ? templates[0]
                : templates[^1];
            var semanticNumber = match.Groups["number"].Value
                .Replace("′", "-prime", StringComparison.Ordinal)
                .Replace("″", "-double-prime", StringComparison.Ordinal);
            return template.Replace("{number}", semanticNumber, StringComparison.Ordinal);
        }

        return null;
    }

    private static TheorySourceFormatException Unknown(string paragraph) => new(
        $"unknown cone numbered claim title '{TheorySourceFormatException.ClaimLead(paragraph)}'");

    private static void ValidateChapter(DigestionAtom atom)
    {
        var chapterNumber = atom.AstPath[(atom.AstPath.IndexOf('/', StringComparison.Ordinal) + 1)..]
            .Split('.')[0];
        var actualChapter = atom.Context.LastOrDefault(static item => item.Level == 2)?.Text;
        var heading = actualChapter is null ? null : ChapterHeadingPattern.Match(actualChapter);
        var actualChapterNumber = heading is { Success: true }
            ? heading.Groups["number"].Value switch
            {
                "〇" => "0", "一" => "1", "二" => "2", "三" => "3",
                "四" => "4", "五" => "5", "六" => "6", "七" => "7",
                "八" => "8", "九" => "9", "十" => "10", "十一" => "11",
                _ => null,
            }
            : null;
        if (actualChapterNumber != chapterNumber)
        {
            throw new TheorySourceFormatException(
                $"cone claim chapter mismatch for {atom.AstPath}: expected chapter {chapterNumber}, got '{actualChapter}'");
        }
    }
}
