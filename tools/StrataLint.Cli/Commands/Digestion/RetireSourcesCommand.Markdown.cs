using System.Collections.Immutable;
using System.Text;
using Markdig;
using Markdig.Syntax;
using Markdig.Syntax.Inlines;

namespace StrataLint.Cli;

internal static partial class RetireSourcesCommand
{
    // Preserve the referent of relative Markdown links when moving the document.
    private static ImmutableArray<byte> ArchiveMarkdown(ImmutableArray<byte> bytes, string source, string destination,
        string[] selectedSources)
    {
        var text = new UTF8Encoding(false, true).GetString(bytes.AsSpan());
        var document = Markdown.Parse(text, new MarkdownPipelineBuilder().UsePreciseSourceLocation().Build());
        var links = document.Descendants<LinkInline>().Where(link => link.Reference is null)
            .Select(link => (link.Url, link.UrlSpan))
            .Concat(document.Descendants<LinkReferenceDefinition>().Select(link => (link.Url, link.UrlSpan)))
            .Distinct().ToArray();
        foreach (var (url, span) in links.OrderByDescending(link => link.UrlSpan.Start))
        {
            if (string.IsNullOrEmpty(url) || url.StartsWith('#') || url.StartsWith('/')
                || Uri.TryCreate(url, UriKind.Absolute, out _)) continue;
            var end = url.IndexOfAny(['?', '#']);
            var path = end < 0 ? url : url[..end];
            var suffix = end < 0 ? string.Empty : url[end..];
            if (path.Length == 0) continue;
            var resolved = Path.GetFullPath(path, Path.GetDirectoryName(Path.GetFullPath(source))!);
            var retiredTarget = selectedSources.SingleOrDefault(candidate => Path.GetFullPath(candidate) == resolved);
            if (retiredTarget is not null)
                resolved = Path.GetFullPath(ArchiveRoot + retiredTarget[TheoryRoot.Length..]);
            var relative = Path.GetRelativePath(Path.GetDirectoryName(Path.GetFullPath(destination))!, resolved)
                .Replace(Path.DirectorySeparatorChar, '/');
            if (span.Start < 0 || span.End < span.Start || span.End >= text.Length)
                throw new FormatException("ARCHIVE_LINK_SPAN_INVALID");
            text = text[..span.Start] + relative + suffix + text[(span.End + 1)..];
        }
        return [.. Encoding.UTF8.GetBytes(text)];
    }
}
