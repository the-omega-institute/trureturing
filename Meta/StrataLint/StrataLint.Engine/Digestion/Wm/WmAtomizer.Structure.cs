using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class WmAtomizer
{
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
