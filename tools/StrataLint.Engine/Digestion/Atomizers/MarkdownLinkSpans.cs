using System.Collections.Immutable;
using Markdig;
using Markdig.Syntax;
using Markdig.Syntax.Inlines;

namespace StrataLint.Engine;

public static class MarkdownLinkSpans
{
    // Offsets identify destination text only, preserving surrounding Markdown.
    public static ImmutableArray<(string? Url, int Start, int End)> Read(string text)
    {
        var document = Markdown.Parse(text, new MarkdownPipelineBuilder().UseMathematics().UsePreciseSourceLocation().Build());
        return document.Descendants<LinkInline>().Where(link => link.Reference is null)
            .Select(link => (link.Url, link.UrlSpan.Start, link.UrlSpan.End))
            .Concat(document.Descendants<LinkReferenceDefinition>().Select(link => (link.Url, link.UrlSpan.Start, link.UrlSpan.End)))
            .Distinct().ToImmutableArray();
    }
}
