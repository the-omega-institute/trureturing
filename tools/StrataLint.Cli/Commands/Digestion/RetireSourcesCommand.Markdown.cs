using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class RetireSourcesCommand
{
    // Preserve the referent of relative Markdown links when moving the document.
    private static ImmutableArray<byte> ArchiveMarkdown(ImmutableArray<byte> bytes, string source, string destination,
        string[] selectedSources)
    {
        var text = new UTF8Encoding(false, true).GetString(bytes.AsSpan());
        foreach (var (url, start, endOffset) in MarkdownLinkSpans.Read(text).OrderByDescending(link => link.Start))
        {
            if (string.IsNullOrEmpty(url) || url.StartsWith('#') || url.StartsWith('/')
                || Uri.TryCreate(url, UriKind.Absolute, out _)) continue;
            var end = url.IndexOfAny(['?', '#']);
            var path = end < 0 ? url : url[..end];
            var suffix = end < 0 ? string.Empty : url[end..];
            if (path.Length == 0) continue;
            var resolved = Path.GetFullPath(Uri.UnescapeDataString(path), Path.GetDirectoryName(Path.GetFullPath(source))!);
            var retiredTarget = selectedSources.SingleOrDefault(candidate => Path.GetFullPath(candidate) == resolved);
            if (retiredTarget is not null)
                resolved = Path.GetFullPath(ArchiveRoot + retiredTarget[TheoryRoot.Length..]);
            var relative = Path.GetRelativePath(Path.GetDirectoryName(Path.GetFullPath(destination))!, resolved)
                .Replace(Path.DirectorySeparatorChar, '/');
            relative = string.Join('/', relative.Split('/').Select(part => part is "." or ".." ? part : Uri.EscapeDataString(part)));
            if (start < 0 || endOffset < start || endOffset >= text.Length)
                throw new FormatException("ARCHIVE_LINK_SPAN_INVALID");
            text = text[..start] + relative + suffix + text[(endOffset + 1)..];
        }
        return [.. Encoding.UTF8.GetBytes(text)];
    }
}
