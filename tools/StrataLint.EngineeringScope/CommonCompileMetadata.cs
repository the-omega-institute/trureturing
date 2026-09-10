using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record CompileMetadataRecord(int Version, string[] Packages, string[] MaterialPaths);

internal static class CommonCompileMetadata
{
    private const string RootPath = CommonExecutionEvidence.RootPath + "/compile-metadata";
    internal const string ManifestPath = RootPath + "/metadata.json";

    internal static string[] Export(string root, RepositorySnapshot snapshot,
        ExecutionMaterial[] nativeMaterials)
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
            var path = Path.Combine(root, CommonBuildOutputs.PackagesPath, PackageKey(id, version));
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
        var references = new List<string>();
        var bound = nativeMaterials.Select(material => material.Path).ToHashSet(StringComparer.Ordinal);
        foreach (var path in paths)
        {
            var package = packages.FirstOrDefault(pair => path.StartsWith(pair.Value + Path.DirectorySeparatorChar, StringComparison.Ordinal));
            if (package.Key is null) continue; // Platform references come from the recipient's pinned runtime.
            var relative = Path.GetRelativePath(root, path).Replace('\\', '/');
            if (!bound.Contains(relative)) throw new InvalidDataException("compile metadata is outside native inventory: " + relative);
            references.Add(relative);
        }
        CommonExecutionEvidence.Write(root, ManifestPath, new CompileMetadataRecord(2,
            packages.Keys.Order(StringComparer.Ordinal).ToArray(), references.ToArray()));
        return [ManifestPath];
    }

    internal static Func<IEnumerable<ScribeCompilationProject>, IReadOnlyList<string>> Load(
        string root, IEnumerable<ExecutionMaterial> engineeringMaterials)
    {
        var bound = engineeringMaterials.ToHashSet();
        var manifest = bound.SingleOrDefault(material => material.Path == ManifestPath)
            ?? throw new InvalidDataException("engineering has no bound compile metadata");
        CommonExecutionEvidence.ValidateMaterials(root, [manifest]);
        var record = CommonExecutionEvidence.Read<CompileMetadataRecord>(root, ManifestPath);
        if (record.Version != 2 || record.Packages.Distinct(StringComparer.Ordinal).Count() != record.Packages.Length
            || record.MaterialPaths.Distinct(StringComparer.Ordinal).Count() != record.MaterialPaths.Length)
            throw new InvalidDataException("invalid compile metadata version or duplicate reference");
        var materials = record.MaterialPaths.Select(path => bound.SingleOrDefault(material => material.Path == path)
            ?? throw new InvalidDataException($"unbound compile metadata: {path}")).ToArray();
        CommonExecutionEvidence.ValidateMaterials(root, materials);
        var packages = record.Packages.ToHashSet(StringComparer.Ordinal);
        var paths = materials.Select(material => Path.Combine(root, material.Path)).ToHashSet(StringComparer.Ordinal);
        string Locate(string id, string version)
        {
            var key = PackageKey(id, version);
            if (!packages.Contains(key)) throw new InvalidDataException($"compile metadata package was not handed off: {key}");
            return Path.Combine(root, CommonBuildOutputs.PackagesPath, key);
        }
        return projects =>
        {
            var inputs = ScribeMetadataReferenceResolver.DescribeInputPaths(projects, Locate);
            foreach (var path in inputs)
                if (path.StartsWith(Path.Combine(root, CommonBuildOutputs.PackagesPath) + Path.DirectorySeparatorChar, StringComparison.Ordinal)
                    && !paths.Contains(path)) throw new InvalidDataException("unbound resolved compile metadata: " + path);
            return inputs;
        };
    }

    private static string PackageKey(string id, string version) => id.ToLowerInvariant() + "/" + version.ToLowerInvariant();
}
