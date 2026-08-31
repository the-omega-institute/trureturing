using Microsoft.CodeAnalysis;
using System.Globalization;
using System.Text.Json;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal sealed record ScribeMetadataDegradation(
    string ProjectPath,
    string Reason,
    bool NeedsXunitAttributeFallback);

internal sealed record ScribeMetadataReferenceResolution(
    IReadOnlyList<MetadataReference> References,
    ScribeMetadataDegradation? Degradation);

internal static class ScribeMetadataReferenceResolver
{
    private static readonly (string Assembly, string Provider)[] RequiredXunitMetadata =
    [
        ("xunit.core", "xunit.extensibility.core"),
        ("xunit.assert", "xunit.assert"),
    ];

    internal static ScribeMetadataReferenceResolution Resolve(ScribeCompilationProject project)
    {
        var paths = PlatformPaths().ToList();
        var assemblyNames = paths
            .Select(Path.GetFileNameWithoutExtension)
            .ToHashSet(StringComparer.OrdinalIgnoreCase);
        var packages = Packages(project).ToArray();
        foreach (var package in packages)
        {
            foreach (var path in CompileAssets(package.Id, package.Version))
            {
                if (assemblyNames.Add(Path.GetFileNameWithoutExtension(path))) paths.Add(path);
            }
        }
        ScribeMetadataDegradation? degradation = null;
        if (ScribeProjectCompilationContext.IsXunitProject(project.ProjectContent))
        {
            var missing = RequiredXunitMetadata
                .Where(metadata => !assemblyNames.Contains(metadata.Assembly))
                .ToArray();
            if (missing.Length != 0)
            {
                if (project.PackageLockContent is not { Length: > 0 })
                {
                    throw new InvalidOperationException(
                        $"xUnit compile assets are unavailable for {project.Path}; "
                        + "the project has no locked package graph");
                }
                var absentProviders = missing
                    .Where(metadata => !packages.Any(package => string.Equals(
                        package.Id,
                        metadata.Provider,
                        StringComparison.OrdinalIgnoreCase)))
                    .ToArray();
                if (absentProviders.Length != 0)
                {
                    throw new InvalidOperationException(
                        $"xUnit compile assets are unavailable for {project.Path}; the locked package graph "
                        + "does not resolve metadata providers: "
                        + string.Join(", ", absentProviders.Select(static metadata =>
                            $"{metadata.Assembly} <- {metadata.Provider}")));
                }
                degradation = new ScribeMetadataDegradation(
                    project.Path,
                    "xUnit compile assets are unavailable from the local NuGet cache "
                    + $"(missing locked assemblies: {string.Join(", ", missing.Select(static item => item.Assembly))})",
                    missing.Any(static item => item.Assembly == "xunit.core"));
            }
        }
        return new ScribeMetadataReferenceResolution(
            paths.Select(static path => MetadataReference.CreateFromFile(path)).ToArray(),
            degradation);
    }

    internal static IEnumerable<MetadataReference> PlatformReferences() =>
        PlatformPaths().Select(static path => MetadataReference.CreateFromFile(path));

    private static IEnumerable<(string Id, string Version)> Packages(ScribeCompilationProject project)
    {
        if (project.PackageLockContent is { Length: > 0 } packageLock)
        {
            using var document = JsonDocument.Parse(packageLock);
            var frameworks = document.RootElement.GetProperty("dependencies");
            var framework = frameworks.EnumerateObject()
                .OrderByDescending(static property => FrameworkScore(property.Name))
                .First().Value;
            foreach (var package in framework.EnumerateObject())
            {
                if (package.Value.TryGetProperty("type", out var type)
                    && type.GetString() == "Project")
                {
                    continue;
                }
                if (package.Value.TryGetProperty("resolved", out var resolved)
                    && resolved.GetString() is { Length: > 0 } version)
                {
                    yield return (package.Name, version);
                }
            }
            yield break;
        }

        var projectDocument = XDocument.Load(new StringReader(project.ProjectContent), LoadOptions.None);
        var pending = new Queue<(string Id, string Version)>(projectDocument.Descendants()
            .Where(static element => element.Name.LocalName == "PackageReference")
            .Select(element => (
                Id: (string?)element.Attribute("Include") ?? string.Empty,
                Version: NormalizeVersion((string?)element.Attribute("Version") ?? string.Empty))));
        var visited = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        while (pending.TryDequeue(out var package))
        {
            if (package.Id.Length == 0 || package.Version.Length == 0 || !visited.Add(package.Id)) continue;
            yield return package;
            foreach (var dependency in PackageDependencies(package.Id, package.Version))
            {
                pending.Enqueue(dependency);
            }
        }
    }

    private static IEnumerable<(string Id, string Version)> PackageDependencies(
        string id,
        string version)
    {
        var directory = PackageDirectory(id, version);
        var nuspec = Directory.Exists(directory)
            ? Directory.EnumerateFiles(directory, "*.nuspec", SearchOption.TopDirectoryOnly).FirstOrDefault()
            : null;
        if (nuspec is null) yield break;
        var document = XDocument.Load(nuspec, LoadOptions.None);
        foreach (var dependency in document.Descendants()
                     .Where(static element => element.Name.LocalName == "dependency"))
        {
            var dependencyId = (string?)dependency.Attribute("id");
            var dependencyVersion = NormalizeVersion((string?)dependency.Attribute("version") ?? string.Empty);
            if (!string.IsNullOrEmpty(dependencyId) && dependencyVersion.Length != 0)
            {
                yield return (dependencyId, dependencyVersion);
            }
        }
    }

    private static IEnumerable<string> CompileAssets(string id, string version)
    {
        var package = PackageDirectory(id, version);
        if (!Directory.Exists(package)) yield break;
        var directory = new[] { "ref", "lib" }
            .Select(root => Path.Combine(package, root))
            .Where(Directory.Exists)
            .SelectMany(root => Directory.EnumerateDirectories(root))
            .OrderByDescending(path => FrameworkScore(Path.GetFileName(path)))
            .FirstOrDefault();
        if (directory is null) yield break;
        foreach (var path in Directory.EnumerateFiles(directory, "*.dll", SearchOption.TopDirectoryOnly)
                     .Order(StringComparer.Ordinal))
        {
            yield return path;
        }
    }

    private static string PackageDirectory(string id, string version) => Path.Combine(
        Environment.GetFolderPath(Environment.SpecialFolder.UserProfile),
        ".nuget",
        "packages",
        id.ToLowerInvariant(),
        version.ToLowerInvariant());

    private static string NormalizeVersion(string version)
    {
        var normalized = version.Trim().Trim('[', ']', '(', ')');
        return normalized.Split(',', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries)
            .FirstOrDefault() ?? string.Empty;
    }

    private static int FrameworkScore(string framework)
    {
        var value = framework.ToLowerInvariant();
        if (value.StartsWith("netstandard", StringComparison.Ordinal))
        {
            return value.StartsWith("netstandard2.1", StringComparison.Ordinal) ? 210 : 200;
        }
        if (!value.StartsWith("net", StringComparison.Ordinal)
            || value.StartsWith("netcoreapp", StringComparison.Ordinal)
            || value.Length < 4
            || !char.IsDigit(value[3]))
        {
            return value.StartsWith("netcoreapp", StringComparison.Ordinal) ? 300 : 0;
        }
        var version = value[3..].Split('-', 2)[0];
        var majorText = version.Split('.', 2)[0];
        return int.TryParse(majorText, CultureInfo.InvariantCulture, out var major) && major <= 10
            ? 400 + major
            : 0;
    }

    private static IReadOnlyList<string> PlatformPaths()
    {
        var runtimeDirectory = Path.GetDirectoryName(typeof(object).Assembly.Location)
            ?? throw new InvalidOperationException("runtime assembly directory is unavailable");
        return (AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES") as string
            ?? throw new InvalidOperationException("runtime platform assemblies are unavailable"))
            .Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
            .Where(path => string.Equals(
                Path.GetDirectoryName(path),
                runtimeDirectory,
                StringComparison.Ordinal))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
    }
}
