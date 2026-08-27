using Jint;
using Jint.Runtime;

// `Engine` alone would bind to the StrataLint.Engine namespace.
using JintEngine = Jint.Engine;

namespace StrataLint.Scribe;

/// <summary>
/// The published site's own parser, run in-process over the vendored
/// <c>tools/vendor/katex/katex.min.js</c>. A hand-maintained approximation of KaTeX's
/// grammar is what let `T^{*}^{k}` reach the site, so the gate asks KaTeX itself.
/// </summary>
internal sealed class KatexParser
{
    internal const string VendorRelativePath = "tools/vendor/katex/katex.min.js";

    // Parsing is the whole job, so the harness never touches KaTeX's HTML: `verdict`
    // returns the parse error or an empty string. `strict` stays off because it turns
    // renderable-but-unidiomatic input (a display-mode `\\`, which this corpus emits by
    // the thousand) into a warning stream the site does not act on either.
    private const string VerdictFunction = """
        function __trureturingKatexVerdict(tex, displayMode) {
          try {
            katex.renderToString(tex, {
              displayMode: displayMode,
              throwOnError: true,
              strict: false,
              trust: false,
            });
            return '';
          } catch (error) {
            return String(error && error.message ? error.message : error);
          }
        }
        """;

    private readonly JintEngine engine;

    private KatexParser(JintEngine engine, string version)
    {
        this.engine = engine;
        Version = version;
    }

    /// <summary>The pinned KaTeX version, as the bundle itself reports it.</summary>
    internal string Version { get; }

    internal static KatexParser Load(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var path = Path.Combine(repositoryRoot, VendorRelativePath);
        if (!File.Exists(path))
        {
            throw new InvalidOperationException(
                $"vendored KaTeX is missing at {VendorRelativePath}");
        }

        var engine = new JintEngine(options => options
            .LimitRecursion(4096)
            .TimeoutInterval(TimeSpan.FromMinutes(1)));
        try
        {
            engine.Execute(File.ReadAllText(path));
            engine.Execute(VerdictFunction);
            var version = engine.Evaluate("katex.version").AsString();
            return new KatexParser(engine, version);
        }
        catch (JavaScriptException exception)
        {
            throw new InvalidOperationException(
                $"vendored KaTeX did not load: {exception.Message}",
                exception);
        }
    }

    /// <summary>
    /// The parse error KaTeX raises for <paramref name="tex"/>, or null when it parses.
    /// </summary>
    internal string? Reject(string tex, bool displayMode)
    {
        ArgumentNullException.ThrowIfNull(tex);
        var verdict = engine
            .Invoke("__trureturingKatexVerdict", tex, displayMode)
            .AsString();
        return verdict.Length == 0 ? null : verdict;
    }
}
