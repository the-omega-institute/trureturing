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
    /// One problem is one file directly under <c>Problems/</c>. Nested directories and
    /// non-Markdown payloads are rejected here so that the pool cannot grow a private
    /// sub-namespace, and any aggregate index would still have to parse as a candidate.
    /// </summary>
    internal static bool IsCanonicalPath(string path) => CanonicalPath.IsMatch(path);

    internal static bool IsCanonicalSlug(string slug) => CanonicalSlug.IsMatch(slug);
}
