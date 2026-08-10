using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static partial class RepositoryPathPolicy
{
    // The canonical values projection address. It stays here rather than with the
    // producer because Scribe references Engine and not the other way round; a second
    // copy of this literal would be a second source of truth for the same address.
    internal const string ValuesProjectionPath = "Evidence/D5/values.json";

    // The canonical anchor catalog address, here for the same reason as the values
    // address: Engine is the lowest layer that names it, and Scribe and Cli reference
    // Engine rather than the reverse. Until #1122 this literal was owned by
    // AnchorCatalogLoader, whose only surviving purpose had become holding it.
    internal const string AnchorCatalogPath = "Meta/StrataLint/Generated/anchor-catalog.v1.json";

    private static readonly Regex CamelPattern = new(
        "^[A-Z][A-Za-z0-9]*$",
        RegexOptions.CultureInvariant);

    private static bool TryDescribeSemanticPath(
        string path,
        out string gid,
        out string label,
        out string? reason)
    {
        gid = string.Empty;
        reason = null;
        if (path.StartsWith("D5/", StringComparison.Ordinal))
        {
            label = "formal";
            if (!path.EndsWith(".lean", StringComparison.Ordinal))
            {
                reason = "path is not a canonical semantic artifact";
                return true;
            }

            gid = path[..^5];
            return true;
        }

        if (path.StartsWith("Blueprint/", StringComparison.Ordinal))
        {
            label = "Blueprint";
            if (!path.StartsWith("Blueprint/D5/", StringComparison.Ordinal)
                || !path.EndsWith(".md", StringComparison.Ordinal))
            {
                reason = "path is not a canonical semantic artifact";
                return true;
            }

            gid = "D5/B/" + path["Blueprint/D5/".Length..^3];
            return true;
        }

        if (path.StartsWith("Evidence/", StringComparison.Ordinal))
        {
            label = "Evidence";
            if (!path.StartsWith("Evidence/D5/", StringComparison.Ordinal))
            {
                reason = "path is not a canonical semantic artifact";
                return true;
            }

            if (string.Equals(path, ValuesProjectionPath, StringComparison.Ordinal))
            {
                gid = "D5/E/values--json";
                return true;
            }

            var relative = path["Evidence/D5/".Length..];
            var slash = relative.LastIndexOf('/');
            var prefix = slash < 0 ? string.Empty : relative[..(slash + 1)];
            var file = slash < 0 ? relative : relative[(slash + 1)..];
            var pieces = file.Split('.');
            if (pieces.Length != 3)
            {
                reason = "Evidence filename needs module.selector.kind";
                return true;
            }

            gid = $"D5/E/{prefix}{pieces[0]}.{pieces[1]}--{pieces[2]}";
            return true;
        }

        var chronicle = Regex.Match(
            path,
            "^Chronicle/([0-9]{4})/([0-9]{2})/([0-9]{2})-([A-Za-z0-9_.-]+)\\.md$",
            RegexOptions.CultureInvariant);
        if (path.StartsWith("Chronicle/", StringComparison.Ordinal))
        {
            label = "Chronicle";
            if (!chronicle.Success)
            {
                reason = "path is not a canonical semantic artifact";
                return true;
            }

            gid = $"D5/C/{chronicle.Groups[1].Value}-{chronicle.Groups[2].Value}-{chronicle.Groups[3].Value}/{chronicle.Groups[4].Value}";
            return true;
        }

        if (path.StartsWith("Library/", StringComparison.Ordinal))
        {
            label = "Library";
            var rootNote = Regex.Match(
                path,
                "^Library/notes/([A-Za-z0-9_.-]+)\\.md$",
                RegexOptions.CultureInvariant);
            if (rootNote.Success)
            {
                gid = "D5/L/" + rootNote.Groups[1].Value;
                return true;
            }

            var splitNote = Regex.Match(
                path,
                "^Library/([A-Z][A-Za-z0-9]*)/([A-Za-z0-9_.-]+)\\.md$",
                RegexOptions.CultureInvariant);
            if (!splitNote.Success)
            {
                reason = "path is not a canonical semantic artifact";
                return true;
            }

            gid = $"D5/L/{splitNote.Groups[1].Value}/{splitNote.Groups[2].Value}";
            return true;
        }

        if (path.StartsWith("Papers/", StringComparison.Ordinal))
        {
            label = "Papers";
            if (path.StartsWith("Papers/recipes/", StringComparison.Ordinal)
                && path.EndsWith(".yaml", StringComparison.Ordinal))
            {
                gid = "D5/P/" + path["Papers/recipes/".Length..^5];
                return true;
            }

            var frozen = Regex.Match(
                path,
                "^Papers/frozen/(D5-P[0-9]{3})/manifest\\.sha256$",
                RegexOptions.CultureInvariant);
            if (frozen.Success)
            {
                gid = $"D5/P/{frozen.Groups[1].Value}--frozen";
                return true;
            }

            reason = "path is not a canonical semantic artifact";
            return true;
        }

        label = string.Empty;
        return false;
    }

    private static bool IsCanonicalBlueprintDefinitionSource(string path)
    {
        const string suffix = ".scribe.cs";
        if (!path.StartsWith("Blueprint/D5/", StringComparison.Ordinal)
            || !path.EndsWith(suffix, StringComparison.Ordinal))
        {
            return false;
        }

        var markdownPath = path[..^suffix.Length] + ".md";
        return TryDescribeSemanticPath(markdownPath, out var gidText, out _, out var reason)
            && reason is null
            && Gid.TryParse(gidText, out var gid)
            && string.Equals(gid.Path.Value, markdownPath, StringComparison.Ordinal);
    }

    private static string InferParseFailure(string path, string label)
    {
        var fileName = path[(path.LastIndexOf('/') + 1)..];
        var module = fileName.Split('.')[0];
        if (!CamelPattern.IsMatch(module) && label is "formal" or "Evidence")
        {
            return "formal module must be CamelCase";
        }

        if (label is "formal" or "Blueprint")
        {
            return "formal address must be Sn/Domain[/SubDomain]/Module or X_Zone/Module";
        }

        return "path is not a canonical semantic artifact";
    }

    private static bool IsCanonicalFutureCoordinate(string path)
    {
        var match = Regex.Match(
            path,
            "^(?<prefix>(?:Blueprint/|Evidence/)?)D(?<theory>[0-9]+)/",
            RegexOptions.CultureInvariant);
        if (!match.Success || match.Groups["theory"].Value == "5")
        {
            return false;
        }

        var candidate = path[..match.Groups["prefix"].Length]
            + "D5/"
            + path[(match.Index + match.Length)..];
        return RepoPath.TryCreate(candidate, out var candidatePath)
            && TryDescribeSemanticPath(candidate, out var gidText, out _, out var reason)
            && reason is null
            && Gid.TryParse(gidText, out var gid)
            && gid.Path == candidatePath;
    }
}
