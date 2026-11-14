using System.Collections.Immutable;
using Markdig;
using Markdig.Syntax;
using Markdig.Syntax.Inlines;

namespace StrataLint.Engine;

internal static class MarkdownLinkSpans
{
    // Offsets identify destination text only, preserving surrounding Markdown.
    public static ImmutableArray<(string? Url, int Start, int End)> Read(string text)
    {
        var document = Markdown.Parse(text, new MarkdownPipelineBuilder().UseMathematics().UsePreciseSourceLocation().Build());
        var opaque = MarkdigBlockAst.LegacyDisplaySpans(text);
        return document.Descendants<LinkInline>().Where(link => link.Reference is null)
            .Select(link => (link.Url, link.UrlSpan.Start, link.UrlSpan.End))
            .Concat(document.Descendants<LinkReferenceDefinition>().Select(link => (link.Url, link.UrlSpan.Start, link.UrlSpan.End)))
            .Where(link => !opaque.Any(span => link.Start >= span.Start && link.End <= span.End))
            .Distinct().ToImmutableArray();
    }
}
