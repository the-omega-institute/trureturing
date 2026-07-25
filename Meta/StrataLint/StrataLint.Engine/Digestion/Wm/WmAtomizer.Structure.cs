using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class WmAtomizer
{
    private const string AppendedAuditClosureMarker = "旧块不改。";
    private const string CurrentTodoClosureMarker =
        "**v0.2**(新行追加于版本账,本节追加 v0.2 校核块)。";

    private static void ValidateClosure(
        string text,
        ImmutableArray<MarkdownBlock> blocks,
        WmAuditBlock[] auditBlocks,
        WmAuditBlock[] appendedAudits)
    {
        var paragraphs = blocks.OfType<MarkdownParagraph>().ToArray();
        var currentTodoClosures = paragraphs
            .Where(paragraph => IsUniqueClosure(
                paragraph.Text,
                CurrentTodoClosurePattern,
                CurrentTodoClosureMarker))
            .ToArray();
        var v01Audits = auditBlocks.Where(static audit => audit.Revision == 1).ToArray();
        if (currentTodoClosures.Length != 1
            || v01Audits.Length != 1
            || currentTodoClosures[0].Start <= v01Audits[0].Paragraph.End
            || appendedAudits.Length > 0
                && currentTodoClosures[0].End >= appendedAudits[0].Paragraph.Start)
        {
            throw new TheorySourceFormatException(
                "WM current-todo closure must occur once after v0.1 audit and before appended audits");
        }

        for (var index = 0; index < appendedAudits.Length; index++)
        {
            var audit = appendedAudits[index];
            var closure = AppendedAuditClosurePattern.Match(audit.Paragraph.Text);
            if (!closure.Success
                || ParseRevision(closure, "WM appended audit closure") != audit.Revision
                || CountOccurrences(audit.Paragraph.Text, AppendedAuditClosureMarker) != 1)
            {
                throw new TheorySourceFormatException(
                    $"WM v0.{audit.Revision} audit block must end with exactly one closure marker");
            }

            if (index < appendedAudits.Length - 1
                && text[audit.Paragraph.End..appendedAudits[index + 1].Paragraph.Start]
                    is not ("\n" or "\r\n" or "\r"))
            {
                throw new TheorySourceFormatException(
                    $"WM appended audit v0.{audit.Revision} must end at its closure paragraph");
            }
        }

        var tail = appendedAudits.Length > 0
            ? appendedAudits[^1].Paragraph
            : currentTodoClosures[0];
        if (tail.End != text.Length)
        {
            throw new TheorySourceFormatException(
                "WM source has missing audit closure or trailing conversation residue");
        }
    }

    private static bool IsUniqueClosure(string paragraph, Regex pattern, string marker) =>
        pattern.IsMatch(paragraph)
        && CountOccurrences(paragraph, marker) == 1
        && paragraph.EndsWith(marker, StringComparison.Ordinal);

    private static int CountOccurrences(string text, string marker)
    {
        var count = 0;
        var offset = 0;
        while ((offset = text.IndexOf(marker, offset, StringComparison.Ordinal)) >= 0)
        {
            count++;
            offset += marker.Length;
        }

        return count;
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
