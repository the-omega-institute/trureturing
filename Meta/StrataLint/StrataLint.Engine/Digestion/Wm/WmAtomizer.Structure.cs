using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class WmAtomizer
{
    private const string V02AuditClosureMarker = "旧块不改。";
    private const string CurrentTodoClosureMarker =
        "**v0.2**(新行追加于版本账,本节追加 v0.2 校核块)。";

    private static void ValidateClosure(
        string text,
        ImmutableArray<MarkdownBlock> blocks,
        bool hasV02Audit)
    {
        var pattern = hasV02Audit ? V02AuditClosurePattern : CurrentTodoClosurePattern;
        var marker = hasV02Audit ? V02AuditClosureMarker : CurrentTodoClosureMarker;
        var closures = blocks.OfType<MarkdownParagraph>()
            .Where(paragraph => IsUniqueTailClosure(paragraph.Text, pattern, marker))
            .ToArray();
        if (closures.Length != 1 || closures[0].End != text.Length)
        {
            throw new TheorySourceFormatException(
                "WM source has missing audit closure or trailing conversation residue");
        }
    }

    private static bool IsUniqueTailClosure(string paragraph, Regex pattern, string marker)
    {
        var firstMarker = paragraph.IndexOf(marker, StringComparison.Ordinal);
        return pattern.IsMatch(paragraph)
            && firstMarker >= 0
            && firstMarker == paragraph.Length - marker.Length;
    }

    private static void ValidateDiscipline(
        string text,
        ImmutableArray<MarkdownBlock> blocks,
        MarkdownHeading[] headings,
        string lastVersionLead)
    {
        var disciplines = blocks.OfType<MarkdownParagraph>()
            .Where(static paragraph => DisciplinePattern.IsMatch(paragraph.Text))
            .ToArray();
        if (disciplines.Length != 1)
        {
            throw new TheorySourceFormatException(
                "WM source must contain exactly one two-line > 一句话: / > 纪律: discipline block");
        }

        var discipline = disciplines[0];
        var lastVersionStart = text.LastIndexOf(lastVersionLead, StringComparison.Ordinal);
        var sectionZeroStart = headings.Single(static heading =>
            IdentifyHeading(heading.Text) == "section/0").Start;
        if (lastVersionStart < 0
            || discipline.Start <= lastVersionStart + lastVersionLead.Length
            || discipline.End >= sectionZeroStart
            || !HasCanonicalDisciplineSeparator(text[discipline.End..sectionZeroStart]))
        {
            throw new TheorySourceFormatException(
                "WM discipline block must follow the version ledger and precede section 0 with its canonical divider");
        }
    }

    private static bool HasCanonicalDisciplineSeparator(string separator) =>
        separator is "\n---\n\n" or "\r\n---\r\n\r\n" or "\r---\r\r";
}
