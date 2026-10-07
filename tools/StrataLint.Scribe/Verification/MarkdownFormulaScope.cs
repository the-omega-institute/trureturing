using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Scribe;

/// <summary>
/// Parses scoped formulas with the site's KaTeX. Selected definitions have both their
/// current render and committed markdown judged; a markdown-only change is judged from
/// its committed bytes without executing its definition. Freshness stays ungated.
/// </summary>
internal sealed class MarkdownFormulaScope
{
    private const string MarkdownSuffix = ".md";
    private const string SourceSuffix = ".scribe.cs";

    private readonly string repositoryRoot;
    private readonly ImmutableHashSet<string> paths;
    private readonly Func<KatexParser> loadParser;
    private readonly ImmutableArray<string>.Builder findings = ImmutableArray.CreateBuilder<string>();
    private readonly HashSet<string> claimed = new(StringComparer.Ordinal);
    private KatexParser? parser;

    /// <summary>
    /// Takes the change's paths verbatim; a Scribe source names the markdown it projects,
    /// and anything outside Blueprint names no document and is dropped.
    /// </summary>
    internal MarkdownFormulaScope(
        string repositoryRoot,
        IEnumerable<string> changedPaths,
        Func<KatexParser>? loadParser = null)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(changedPaths);
        this.repositoryRoot = repositoryRoot;
        this.loadParser = loadParser ?? KatexParser.Create;
        paths = changedPaths
            .Select(MarkdownPathOf)
            .OfType<string>()
            .ToImmutableHashSet(StringComparer.Ordinal);
    }

    /// <summary>
    /// The NUL-separated repository-relative paths a caller hands in, as `git diff -z`
    /// writes them: a path may hold anything but NUL, so nothing weaker separates them.
    /// </summary>
    internal static ImmutableArray<string> ParsePaths(string payload)
    {
        ArgumentNullException.ThrowIfNull(payload);
        return
        [
            .. payload
                .Split('\0', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries)
                .Distinct(StringComparer.Ordinal)
                .Order(StringComparer.Ordinal),
        ];
    }

    /// <summary>The markdown projections this scope names.</summary>
    internal ImmutableHashSet<string> Paths => paths;

    /// <summary>The scoped documents whose formulas were inspected.</summary>
    internal int Judged { get; private set; }

    /// <summary>The distinct formulas parsed across those documents.</summary>
    internal int Formulas { get; private set; }

    internal ImmutableArray<string> Findings => findings.ToImmutable();

    /// <summary>
    /// Judges the scoped documents, rendering those and only those: a render costs real
    /// time per document and the verdict has to stay proportional to the change.
    /// </summary>
    internal void Judge(
        IEnumerable<DocumentDefinition> definitions,
        Func<DocumentDefinition, ReadOnlyMemory<byte>> render)
    {
        ArgumentNullException.ThrowIfNull(definitions);
        ArgumentNullException.ThrowIfNull(render);
        foreach (var definition in definitions.Where(
            definition => paths.Contains(definition.RelativePath.Value)))
        {
            Inspect(definition, render(definition).Span);
        }

        Close();
    }

    internal void Inspect(DocumentDefinition definition, ReadOnlySpan<byte> rendered)
    {
        ArgumentNullException.ThrowIfNull(definition);
        var relativePath = definition.RelativePath.Value;
        if (!paths.Contains(relativePath))
        {
            return;
        }

        Judged++;
        claimed.Add(relativePath);
        var seen = new HashSet<(bool Display, string Tex)>();
        Judge(relativePath, Encoding.UTF8.GetString(rendered), seen);

        var path = Path.Combine(repositoryRoot, relativePath);
        if (!File.Exists(path))
        {
            return;
        }

        var committed = File.ReadAllBytes(path);
        if (committed.AsSpan().SequenceEqual(rendered))
        {
            return;
        }

        Judge(relativePath, Encoding.UTF8.GetString(committed), seen);
    }

    /// <summary>Judges an existing projection whose definition was not selected.</summary>
    internal void InspectCommitted(string relativePath)
    {
        if (!paths.Contains(relativePath) || claimed.Contains(relativePath))
        {
            return;
        }

        var path = Path.Combine(repositoryRoot, relativePath);
        var source = Path.Combine(repositoryRoot, relativePath[..^MarkdownSuffix.Length] + SourceSuffix);
        if (!File.Exists(path) || !File.Exists(source))
        {
            return;
        }

        claimed.Add(relativePath);
        Judged++;
        Judge(relativePath, Encoding.UTF8.GetString(File.ReadAllBytes(path)), new HashSet<(bool, string)>());
    }

    /// <summary>
    /// Reports existing scoped projections that were neither rendered nor inspected.
    /// </summary>
    internal void Close()
    {
        foreach (var path in paths
                     .Except(claimed, StringComparer.Ordinal)
                     .Where(path => File.Exists(Path.Combine(repositoryRoot, path)))
                     .Order(StringComparer.Ordinal))
        {
            findings.Add($"{path}: no Scribe document renders this markdown");
        }
    }

    /// <summary>The markdown a changed path names, or null when it names none.</summary>
    private static string? MarkdownPathOf(string path)
    {
        if (path is null || !path.StartsWith("Blueprint/", StringComparison.Ordinal))
        {
            return null;
        }

        if (path.EndsWith(SourceSuffix, StringComparison.Ordinal))
        {
            return string.Concat(path.AsSpan(0, path.Length - SourceSuffix.Length), MarkdownSuffix);
        }

        return path.EndsWith(MarkdownSuffix, StringComparison.Ordinal) ? path : null;
    }

    private void Judge(string relativePath, string markdown, HashSet<(bool, string)> seen)
    {
        foreach (var formula in MarkdownMath.Extract(markdown))
        {
            if (!seen.Add((formula.Display, formula.Tex)))
            {
                continue;
            }

            Formulas++;
            parser ??= loadParser();
            if (parser.Reject(formula.Tex, formula.Display) is not { } rejection)
            {
                continue;
            }

            findings.Add($"{relativePath}:{formula.Line}: {rejection.ReplaceLineEndings(" ")}");
        }
    }
}
