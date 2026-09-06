using System.Text.RegularExpressions;

namespace StrataLint.Engine;

/// <summary>
/// The canonical address shape of the literature-sourced problem pool (spec 11.20.3).
/// It lives in Engine because the repository path policy admits these paths and the
/// Scribe catalog parses them; a second copy of the slug rule would be a second source
/// of truth for the same address.
/// </summary>
internal static class ProblemPoolPaths
{
    internal const string DirectoryName = "Problems";

    private static readonly Regex CanonicalPath = new(
        "^Problems/[a-z0-9]+(-[a-z0-9]+)*\\.md$",
        RegexOptions.CultureInvariant);

    private static readonly Regex CanonicalSlug = new(
        "^[a-z0-9]+(-[a-z0-9]+)*$",
        RegexOptions.CultureInvariant);

    /// <summary>
    /// Dossiers have flat Markdown addresses under <c>Problems/</c>. This predicate
    /// checks paths only, not their content or proposition atomicity. A separate
    /// explicit-anchor content contract remains pending.
    /// </summary>
    internal static bool IsCanonicalPath(string path) => CanonicalPath.IsMatch(path);

    internal static bool IsCanonicalSlug(string slug) => CanonicalSlug.IsMatch(slug);
}
