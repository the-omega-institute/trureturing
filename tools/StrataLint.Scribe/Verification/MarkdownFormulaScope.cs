using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Scribe;

/// <summary>
/// Parses the formulas of the documents a change touches with the site's own KaTeX, which
/// is the one thing no other gate does: the emitter's rules are a hand-maintained reading
/// of KaTeX's grammar, and a reading has already been wrong once. Documents outside the
/// change are rendered as usual and left unjudged — a document's bytes depend on the whole
/// graph, but the verdict has to stay proportional to the diff.
///
/// Both sides of a document are judged: the committed markdown is what the site publishes
/// until the next `make emit`, and the current render is what it publishes after. Freshness
/// itself stays ungated, as it is elsewhere — a projection is a reader snapshot.
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
        this.loadParser = loadParser ?? (() => KatexParser.Load(repositoryRoot));
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

    /// <summary>The scoped documents the render actually reached.</summary>
    internal int Judged { get; private set; }

    /// <summary>The distinct formulas parsed across those documents.</summary>
    internal int Formulas { get; private set; }

    internal ImmutableArray<string> Findings => findings.ToImmutable();

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

    /// <summary>
    /// Closes the scope. A scoped path that still exists but no document rendered was
    /// checked by nothing, and saying so beats reporting a green the gate never earned.
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
