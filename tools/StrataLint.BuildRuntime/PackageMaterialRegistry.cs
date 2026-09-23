using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record PackageMaterialRegistration(string PackagePath, string[] Include, string[] Exclude);

internal sealed record PackageMaterialManifest(string PackageRootSource, PackageMaterialRegistration[] Packages);

internal static class PackageMaterialRegistry
{
    internal const string RelativePath = "Meta/package-materials.json";

    internal static PackageMaterialManifest Load(string root)
    {
        try { return Parse(root); }
        catch (JsonException exception) { throw Invalid(exception.Message); }
        catch (FileMapPatternException exception) { throw Invalid(exception.Message); }
    }

    private static PackageMaterialManifest Parse(string root)
    {
        var path = Path.Combine(root, RelativePath);
        if (!File.Exists(path)) throw new InvalidDataException($"package material registry is missing: {RelativePath}");
        using var document = JsonDocument.Parse(File.ReadAllBytes(path));
        var objectRoot = document.RootElement.ValueKind == JsonValueKind.Object
            ? document.RootElement : throw Invalid("registry root must be an object");
        RequireKeys(objectRoot, "schemaVersion", "packageRootSource", "packages");
        if (!objectRoot.TryGetProperty("schemaVersion", out var schema) || schema.ValueKind != JsonValueKind.Number
            || !schema.TryGetInt32(out var version) || version != 1)
            throw Invalid("schemaVersion must be 1");
        var source = String(objectRoot, "packageRootSource");
        if (source != "build-output:NuGetPackageRoot")
            throw Invalid("packageRootSource must be build-output:NuGetPackageRoot");
        if (!objectRoot.TryGetProperty("packages", out var packageArray) || packageArray.ValueKind != JsonValueKind.Array || packageArray.GetArrayLength() == 0)
            throw Invalid("packages must be a non-empty array");
        var rows = new List<PackageMaterialRegistration>();
        foreach (var item in packageArray.EnumerateArray())
        {
            if (item.ValueKind != JsonValueKind.Object) throw Invalid("package registration must be an object");
            RequireKeys(item, "packagePath", "include", "exclude");
            var packagePath = String(item, "packagePath");
            if (!RepoPath.TryCreate(packagePath, out _) || packagePath.Split('/').Length != 2
                || packagePath.IndexOfAny(['*', '?']) >= 0)
                throw Invalid($"invalid packagePath: {packagePath}");
            var include = Patterns(item, "include", packagePath);
            var exclude = Patterns(item, "exclude", packagePath);
            if (include.Length == 0) throw Invalid($"package {packagePath} has no include patterns");
            if (rows.Any(row => row.PackagePath == packagePath))
                throw Invalid($"duplicate package registration: {packagePath}");
            if (include.Intersect(exclude, StringComparer.Ordinal).Any())
                throw Invalid($"conflicting include/exclude pattern for package {packagePath}");
            rows.Add(new(packagePath, include, exclude));
        }
        if (!rows.Select(row => row.PackagePath).SequenceEqual(rows.Select(row => row.PackagePath).Order(StringComparer.Ordinal), StringComparer.Ordinal))
            throw Invalid("package registrations must be ordinally sorted");
        return new(source, rows.ToArray());
    }

    internal static IEnumerable<(string Relative, string Source)> Expand(string root, string packageRoot)
    {
        var manifest = Load(root);
        if (string.IsNullOrWhiteSpace(packageRoot) || !Path.IsPathFullyQualified(packageRoot))
            throw Invalid("NuGetPackageRoot must be an absolute producer-supplied path");
        foreach (var registration in manifest.Packages)
        {
            var directory = Path.Combine(packageRoot, registration.PackagePath);
            var excluded = registration.Exclude.Select(FileMapGlob.Create).ToArray();
            var matched = new SortedSet<string>(StringComparer.Ordinal);
            foreach (var pattern in registration.Include)
            {
                var files = ExpandPattern(directory, pattern).Where(file => !excluded.Any(glob => glob.IsMatch(file))).ToArray();
                if (files.Length == 0)
                    throw Invalid($"missing registered package material: {registration.PackagePath}/{pattern}");
                matched.UnionWith(files);
            }
            foreach (var file in matched)
            {
                var relative = registration.PackagePath + "/" + file;
                if (!RepoPath.TryCreate(relative, out _)) throw Invalid($"invalid registered package material: {relative}");
                yield return (relative, Path.Combine(directory, file));
            }
        }
    }

    private static IEnumerable<string> ExpandPattern(string directory, string pattern)
    {
        var wildcard = pattern.IndexOf('*');
        if (wildcard < 0)
            return File.Exists(Path.Combine(directory, pattern)) ? [pattern] : [];
        var separator = pattern.LastIndexOf('/', wildcard);
        var prefix = separator < 0 ? "" : pattern[..(separator + 1)];
        var searchRoot = Path.Combine(directory, prefix);
        if (!Directory.Exists(searchRoot)) return [];
        var glob = FileMapGlob.Create(pattern);
        var recursive = pattern[(separator + 1)..].Contains('/') || pattern.Contains("**", StringComparison.Ordinal);
        return Directory.EnumerateFiles(searchRoot, "*", recursive ? SearchOption.AllDirectories : SearchOption.TopDirectoryOnly)
            .Select(file => Path.GetRelativePath(directory, file).Replace('\\', '/')).Where(glob.IsMatch);
    }

    private static string[] Patterns(JsonElement item, string name, string packagePath)
    {
        if (!item.TryGetProperty(name, out var value) || value.ValueKind != JsonValueKind.Array)
            throw Invalid($"package {packagePath} {name} must be an array");
        var patterns = value.EnumerateArray().Select(element => element.ValueKind == JsonValueKind.String ? element.GetString()! : throw Invalid($"package {packagePath} {name} contains a non-string" )).ToArray();
        if (patterns.Any(string.IsNullOrWhiteSpace) || patterns.Distinct(StringComparer.Ordinal).Count() != patterns.Length)
            throw Invalid($"package {packagePath} {name} contains duplicate or empty patterns");
        foreach (var pattern in patterns) _ = FileMapGlob.Create(pattern);
        return patterns;
    }

    private static string String(JsonElement item, string name) => item.TryGetProperty(name, out var value) && value.ValueKind == JsonValueKind.String && !string.IsNullOrWhiteSpace(value.GetString())
        ? value.GetString()! : throw Invalid($"{name} must be a non-empty string");

    private static void RequireKeys(JsonElement item, params string[] expected)
    {
        var actual = item.EnumerateObject().Select(property => property.Name).Order(StringComparer.Ordinal).ToArray();
        if (!actual.SequenceEqual(expected.Order(StringComparer.Ordinal), StringComparer.Ordinal))
            throw Invalid($"registry keys must be exactly: {string.Join(", ", expected.Order(StringComparer.Ordinal))}");
    }

    private static InvalidDataException Invalid(string message) => new("Invalid package material registry: " + message);
}
