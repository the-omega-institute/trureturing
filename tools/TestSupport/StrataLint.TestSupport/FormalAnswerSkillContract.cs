using System.Text;
using System.Text.RegularExpressions;
using Markdig;
using Markdig.Syntax;
using Markdig.Syntax.Inlines;

namespace StrataLint.TestSupport;

internal static class FormalAnswerSkillContract
{
    internal const string MethodAnchorsHeading = "Method anchors";
    internal const string SelfAnchorsHeading = "Self anchors";

    private static readonly MarkdownPipeline Pipeline = new MarkdownPipelineBuilder()
        .UsePipeTables()
        .Build();

    internal static IReadOnlyList<Block> FindSection(
        MarkdownDocument document,
        string headingText)
    {
        var headings = document
            .OfType<HeadingBlock>()
            .Where(heading => PlainText(heading).Equals(headingText, StringComparison.Ordinal))
            .ToArray();

        return headings.Length == 1 ? SectionBlocks(document, headings[0]) : [];
    }

    internal static IReadOnlyList<Block> SectionBlocks(
        MarkdownDocument document,
        HeadingBlock heading)
    {
        var section = new List<Block>();
        var inside = false;

        foreach (var block in document)
        {
            if (ReferenceEquals(block, heading))
            {
                inside = true;
                continue;
            }

            if (!inside)
            {
                continue;
            }

            if (block is HeadingBlock nextHeading && nextHeading.Level <= heading.Level)
            {
                break;
            }

            section.Add(block);
        }

        return section;
    }

    internal static IEnumerable<Block> SelfAndDescendants(Block block)
    {
        yield return block;

        if (block is not ContainerBlock container)
        {
            yield break;
        }

        foreach (var child in container)
        {
            foreach (var descendant in SelfAndDescendants(child))
            {
                yield return descendant;
            }
        }
    }

    internal static IEnumerable<string> InlineCodeValuesFromBlock(Block block)
    {
        foreach (var leaf in SelfAndDescendants(block).OfType<LeafBlock>())
        {
            foreach (var value in InlineCodeValuesFromInline(leaf.Inline?.FirstChild))
            {
                yield return value;
            }
        }
    }

    internal static IEnumerable<string> InlineCodeValuesFromInline(Inline? inline)
    {
        for (var current = inline; current is not null; current = current.NextSibling)
        {
            if (current is CodeInline code)
            {
                yield return code.Content;
            }

            if (current is ContainerInline container)
            {
                foreach (var value in InlineCodeValuesFromInline(container.FirstChild))
                {
                    yield return value;
                }
            }
        }
    }

    internal static string PlainText(LeafBlock block)
    {
        var text = new StringBuilder();
        AppendInlineText(block.Inline?.FirstChild, text);
        return text.ToString();
    }

    internal static void AppendInlineText(Inline? inline, StringBuilder text)
    {
        for (var current = inline; current is not null; current = current.NextSibling)
        {
            switch (current)
            {
                case LiteralInline literal:
                    text.Append(literal.Content);
                    break;
                case CodeInline code:
                    text.Append(code.Content);
                    break;
                case ContainerInline container:
                    AppendInlineText(container.FirstChild, text);
                    break;
            }
        }
    }

    /// <summary>
    /// Each bullet of an anchor registry names a declaration and then the Lean module that
    /// holds it, both as inline code. A bullet with fewer than two codes is kept with an
    /// empty path so that it is reported as unresolved rather than silently skipped.
    /// </summary>
    internal static IReadOnlyList<(string Name, string Path)> AnchorEntries(
        MarkdownDocument document,
        string headingText) =>
        FindSection(document, headingText)
            .SelectMany(SelfAndDescendants)
            .OfType<ListBlock>()
            .Where(list => !list.IsOrdered)
            .SelectMany(list => list.OfType<ListItemBlock>())
            .Select(item => InlineCodeValuesFromBlock(item).ToArray())
            .Where(codes => codes.Length > 0)
            .Select(codes => (Name: codes[0], Path: codes.Length > 1 ? codes[1] : string.Empty))
            .ToArray();

    internal static IReadOnlyList<string> UnresolvedAnchors(
        IReadOnlyList<(string Name, string Path)> anchors,
        IReadOnlyDictionary<string, string> leanSources) =>
        anchors
            .Where(anchor => !leanSources.TryGetValue(anchor.Path, out var source)
                || !Regex.IsMatch(
                    source,
                    @"^theorem\s+" + Regex.Escape(anchor.Name) + @"(?![A-Za-z0-9_'])",
                    RegexOptions.Multiline | RegexOptions.CultureInvariant))
            .Select(anchor => anchor.Name)
            .ToArray();

    internal static MarkdownDocument Parse(string markdown) => Markdown.Parse(markdown, Pipeline);
}
