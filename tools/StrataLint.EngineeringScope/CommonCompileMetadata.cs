using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record CompileMetadataRecord(int Version, string[] Packages, ExecutionMaterial[] Materials);

internal static class CommonCompileMetadata
{
    private const string RootPath = CommonExecutionEvidence.RootPath + "/compile-metadata";
    internal const string ManifestPath = RootPath + "/metadata.json";

    internal static string[] Export(string root, RepositorySnapshot snapshot,
        Func<string, string, string>? packageDirectory = null)
    {
        var destination = Path.Combine(root, RootPath);
        if (Directory.Exists(destination)) Directory.Delete(destination, recursive: true);
        var projects = ScribeProjectCompilationContext.Create(
            snapshot.Files.Values.Where(file => file.Path.Value.EndsWith(".csproj", StringComparison.Ordinal)
                    || file.Path.Value.EndsWith("packages.lock.json", StringComparison.Ordinal))
                .Select(file => new ScribeTrackedSource(file.Path.Value, file.Text)).ToArray(),
            new Dictionary<string, string>(), new HashSet<string>()).Projects;
        var packages = new Dictionary<string, string>(StringComparer.Ordinal);
        string Locate(string id, string version)
        {
            var path = Path.GetFullPath((packageDirectory ?? ScribeMetadataReferenceResolver.PackageDirectory)(id, version));
            if (!Directory.Exists(path)) throw new InvalidDataException($"compile metadata package is unavailable: {id}/{version}");
            packages[PackageKey(id, version)] = path;
            return path;
        }
        IReadOnlyList<string> Inputs(IEnumerable<ScribeCompilationProject> items) =>
            ScribeMetadataReferenceResolver.DescribeInputPaths(items, Locate);
        var paths = Inputs(projects);
        foreach (var project in projects)
            if (ScribeMetadataReferenceResolver.Resolve(project, Inputs).Degradation is { } missing)
                throw new InvalidDataException($"compile metadata is unavailable: {missing.ProjectPath}: {missing.Reason}");
        var copied = new List<string>();
        foreach (var path in paths)
        {
            var package = packages.FirstOrDefault(pair => path.StartsWith(pair.Value + Path.DirectorySeparatorChar, StringComparison.Ordinal));
            if (package.Key is null) continue; // Platform references come from the recipient's pinned runtime.
            var relative = RootPath + "/packages/" + package.Key + "/" + Path.GetRelativePath(package.Value, path).Replace('\\', '/');
            var target = Path.Combine(root, relative);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(path, target, overwrite: true);
            copied.Add(relative);
        }
        CommonExecutionEvidence.Write(root, ManifestPath, new CompileMetadataRecord(1,
            packages.Keys.Order(StringComparer.Ordinal).ToArray(), CommonExecutionEvidence.Materials(root, copied)));
        return copied.Append(ManifestPath).ToArray();
    }

    internal static Func<IEnumerable<ScribeCompilationProject>, IReadOnlyList<string>> Load(
        string root, IEnumerable<ExecutionMaterial> engineeringMaterials)
    {
        var bound = engineeringMaterials.ToHashSet();
        var manifest = bound.SingleOrDefault(material => material.Path == ManifestPath)
            ?? throw new InvalidDataException("engineering has no bound compile metadata");
        CommonExecutionEvidence.ValidateMaterials(root, [manifest]);
        var record = CommonExecutionEvidence.Read<CompileMetadataRecord>(root, ManifestPath);
        if (record.Version != 1) throw new InvalidDataException("invalid compile metadata version");
        foreach (var material in record.Materials)
            if (!bound.Contains(material)) throw new InvalidDataException($"unbound compile metadata: {material.Path}");
        CommonExecutionEvidence.ValidateMaterials(root, record.Materials);
        var packages = record.Packages.ToHashSet(StringComparer.Ordinal);
        string Locate(string id, string version)
        {
            var key = PackageKey(id, version);
            if (!packages.Contains(key)) throw new InvalidDataException($"compile metadata package was not handed off: {key}");
            return Path.Combine(root, RootPath, "packages", key);
        }
        return projects => ScribeMetadataReferenceResolver.DescribeInputPaths(projects, Locate);
    }

    private static string PackageKey(string id, string version) => id.ToLowerInvariant() + "/" + version.ToLowerInvariant();
}
