using System.Text.Json;

namespace StrataLint.Engine;

// Data-only validation shared by current-tree admission and cache writer admission.
// Lake materializes the workspace manifest into the shared packages directory;
// a different pin must be rejected before Lake can change that checkout.
internal static class RegManifestAgreement
{
    internal const string LakefilePath = "Reg/lakefile.toml";
    internal const string ManifestPath = "Reg/lake-manifest.json";

    internal static string? Validate(string? rootManifest, string? regManifest, bool hasLakefile)
    {
        if (regManifest is null)
            return hasLakefile ? "REG-MANIFEST-MISSING: Reg/lakefile.toml requires Reg/lake-manifest.json" : null;
        if (!hasLakefile || rootManifest is null)
            return "REG-MANIFEST-INVALID: Reg requires its lakefile and the root manifest";
        try
        {
            using var root = JsonDocument.Parse(rootManifest);
            using var reg = JsonDocument.Parse(regManifest);
            if (String(reg.RootElement, "packagesDir") != "../.lake/packages")
                return "REG-MANIFEST-PACKAGES-DIR: expected ../.lake/packages";
            var rootPackages = Packages(root.RootElement);
            var regPackages = Packages(reg.RootElement);
            var rootGit = GitEntries(rootPackages);
            var regGit = GitEntries(regPackages);
            if (rootGit.Count != regGit.Count || rootGit.Any(item =>
                    !regGit.TryGetValue(item.Key, out var count) || count != item.Value))
                return "REG-MANIFEST-GIT-AGREEMENT: git package multisets differ from lake-manifest.json";
            if (regPackages.Where(item => String(item, "type") == "git")
                .Any(item => !item.TryGetProperty("inherited", out var inherited)
                    || inherited.ValueKind != JsonValueKind.True))
                return "REG-MANIFEST-INHERITED: every Reg git package must be inherited";
            var paths = regPackages.Where(item => String(item, "type") == "path").ToArray();
            if (paths.Length != 3 || !PathEntry(paths, "trureturing", "..", "lakefile.toml")
                || !PathEntry(paths, "leanInspectorInterface", "../tools/lean-inspector-interface", "lakefile.toml")
                || !PathEntry(paths, "leanInspector", "../tools/lean-inspector", "lakefile.lean"))
                return "REG-MANIFEST-PATH-AGREEMENT: expected exactly the D5, Interface and inspector path requires";
            return null;
        }
        catch (Exception error) when (error is JsonException or InvalidOperationException or FormatException)
        {
            return "REG-MANIFEST-INVALID: " + error.Message;
        }
    }

    private static JsonElement[] Packages(JsonElement manifest)
    {
        if (!manifest.TryGetProperty("packages", out var packages) || packages.ValueKind != JsonValueKind.Array)
            throw new FormatException("packages must be an array");
        var result = packages.EnumerateArray().ToArray();
        foreach (var package in result)
        {
            if (String(package, "type") is not ("git" or "path"))
                throw new FormatException("unknown package type");
        }
        return result;
    }

    private static Dictionary<string, int> GitEntries(IEnumerable<JsonElement> packages) => packages
        .Where(item => String(item, "type") == "git")
        .Select(item => JsonSerializer.Serialize(new[]
        {
            String(item, "name"), String(item, "url"), String(item, "rev"),
            NullableString(item, "inputRev"), NullableString(item, "subDir"),
            String(item, "configFile"), NullableString(item, "manifestFile"),
        }))
        .GroupBy(key => key, StringComparer.Ordinal)
        .ToDictionary(group => group.Key, group => group.Count(), StringComparer.Ordinal);

    private static bool PathEntry(JsonElement[] paths, string name, string directory, string config) =>
        paths.Count(item => String(item, "name") == name
            && String(item, "dir") == directory && String(item, "configFile") == config
            && String(item, "manifestFile") == "lake-manifest.json"
            && item.TryGetProperty("inherited", out var inherited)
            && inherited.ValueKind == JsonValueKind.False) == 1;

    private static string String(JsonElement element, string name) =>
        element.TryGetProperty(name, out var value) && value.ValueKind == JsonValueKind.String
            && value.GetString() is { Length: > 0 } text ? text
            : throw new FormatException($"{name} must be a nonempty string");

    private static string? NullableString(JsonElement element, string name) =>
        element.TryGetProperty(name, out var value)
            ? value.ValueKind == JsonValueKind.Null ? null : String(element, name)
            : throw new FormatException($"missing {name}");
}
