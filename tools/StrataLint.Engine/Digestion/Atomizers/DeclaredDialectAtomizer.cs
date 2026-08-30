using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

/// <summary>
/// Digests a volume whose dialect is declared in data rather than written in code: the
/// claim pattern and the genre table both come from <see cref="DeclaredDialect"/>. A
/// pattern names its own <c>kind</c> and <c>number</c> groups; the locator is the mapped
/// kind over the captured number, which is how every built-in numbered dialect addresses
/// its claims.
/// </summary>
internal static class DeclaredDialectAtomizer
{
    internal const string IdPrefix = "dialect:";

    internal static AtomizedTheoryDocument Atomize(
        string atomizerId,
        ReadOnlySpan<byte> bytes,
        TheoryAtomizerRules rules)
    {
        ArgumentNullException.ThrowIfNull(rules);
        var dialect = Require(atomizerId, rules);
        var pattern = new Regex(dialect.ClaimPattern, RegexOptions.CultureInvariant);
        var unregistered = new SortedSet<string>(StringComparer.Ordinal);
        ImmutableArray<string> Seen() => [.. unregistered];
        return dialect.HeadingClaims
            ? MarkdownAstAtomizer.Atomize(
                bytes,
                static _ => null,
                () => GenreRegistryCheck.Collected(Seen()),
                identifyHeading: heading => Identify(heading, dialect, pattern, unregistered))
            : MarkdownAstAtomizer.Atomize(
                bytes,
                paragraph => Identify(paragraph, dialect, pattern, unregistered),
                () => GenreRegistryCheck.Collected(Seen()));
    }

    internal static DeclaredDialect Require(string atomizerId, TheoryAtomizerRules rules)
    {
        var id = atomizerId[IdPrefix.Length..];
        if (rules.Dialects.TryGetValue(id, out var dialect))
        {
            return dialect;
        }

        throw new FormatException(
            $"Unknown declared dialect '{id}'. Declared dialects: "
            + (rules.Dialects.IsEmpty
                ? "(none)"
                : string.Join(", ", rules.Dialects.Keys.Order(StringComparer.Ordinal)))
            + ".");
    }

    private static string? Identify(
        string paragraph,
        DeclaredDialect dialect,
        Regex pattern,
        SortedSet<string> unregistered)
    {
        var match = pattern.Match(paragraph);
        if (!match.Success)
        {
            return null;
        }

        // Same contract as the built-in dialects: a lead that fits the shape but names no
        // registered genre is addressed by its own token and recorded, never silently skipped
        // and never allowed to cost the volume its other claims. The ledger records it as open.
        var token = match.Groups["kind"].Value;
        var genre = dialect.Genres.FirstOrDefault(item => item.Token == token);
        genre ??= GenreSuffixResolver.Resolve(token, dialect.GenreSuffixes);
        if (genre is null)
        {
            unregistered.Add(token);
        }

        return genre is null ? token : genre.Value;
    }
}
