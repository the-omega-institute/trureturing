using StrataLint.Engine;
using System.Text.Json;
using System.Text.Json.Serialization;
using System.Xml.Linq;

namespace StrataLint.EngineeringScope;

internal sealed record RegisteredCompileAssembly(string Assembly, string Source, string[] Projects);
internal sealed record CompileMetadataRegistration(int Version, RegisteredCompileAssembly[] Assemblies);
internal sealed record CompileMetadataRecord(int Version, string[] Packages,
    RegisteredCompileAssembly[] Assemblies, ExecutionMaterial[] Materials);

internal static class CommonCompileMetadata
{
    private const string RootPath = CommonExecutionEvidence.RootPath + "/compile-metadata";
    internal const string ManifestPath = RootPath + "/metadata.json";
    private const string RegistrationPath = "Meta/compile-metadata.json";
    private static readonly JsonSerializerOptions RegistrationOptions = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
        UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
        AllowDuplicateProperties = false,
    };

    internal static string[] Export(string root, RepositorySnapshot snapshot,
        Func<string, string, string>? packageDirectory = null)
    {
        var destination = Path.Combine(root, RootPath);
        if (Directory.Exists(destination)) Directory.Delete(destination, recursive: true);
        var files = snapshot.Files.Values.Select(file => new ScribeTrackedSource(file.Path.Value, file.Text)).ToArray();
        var projects = ScribeProjectCompilationContext.Create(files, EngineeringProjectRegistry.Read(files)).Projects;
        var assemblies = ReadRegistration(snapshot);
        _ = RegisteredInputs(projects, assemblies).ToArray();
        foreach (var assembly in assemblies)
            RequireMaterial(root, assembly.Source);
        var packages = new Dictionary<string, string>(StringComparer.Ordinal);
        string Locate(string id, string version)
        {
            var path = Path.GetFullPath((packageDirectory ?? ScribeMetadataReferenceResolver.PackageDirectory)(id, version));
            if (!Directory.Exists(path)) throw new InvalidDataException($"compile metadata package is unavailable: {id}/{version}");
            packages[PackageKey(id, version)] = path;
            return path;
        }
        IReadOnlyList<string> Inputs(IEnumerable<ScribeCompilationProject> items) =>
            ScribeMetadataReferenceResolver.DescribeInputPaths(items, Locate)
                .Concat(RegisteredInputs(items, assemblies).Select(assembly => Path.Combine(root, assembly.Source)))
                .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
        var paths = Inputs(projects);
        foreach (var project in projects)
            if (ScribeMetadataReferenceResolver.Resolve(project, Inputs).Degradation is { } missing)
                throw new InvalidDataException($"compile metadata is unavailable: {missing.ProjectPath}: {missing.Reason}");
        var copied = new List<string>();
        foreach (var assembly in assemblies)
        {
            var relative = MaterialPath(assembly);
            var target = Path.Combine(root, relative);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(Path.Combine(root, assembly.Source), target, overwrite: true);
            copied.Add(relative);
        }
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
        CommonExecutionEvidence.Write(root, ManifestPath, new CompileMetadataRecord(2,
            packages.Keys.Order(StringComparer.Ordinal).ToArray(), assemblies, CommonExecutionEvidence.Materials(root, copied)));
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
        if (record.Version != 2) throw new InvalidDataException("invalid compile metadata version");
        ValidateRegistration(record.Assemblies);
        foreach (var material in record.Materials)
            if (!bound.Contains(material)) throw new InvalidDataException($"unbound compile metadata: {material.Path}");
        CommonExecutionEvidence.ValidateMaterials(root, record.Materials);
        foreach (var assembly in record.Assemblies)
            if (!record.Materials.Any(material => material.Path == MaterialPath(assembly)))
                throw new InvalidDataException($"unbound registered compile material: {assembly.Assembly}");
        var packages = record.Packages.ToHashSet(StringComparer.Ordinal);
        string Locate(string id, string version)
        {
            var key = PackageKey(id, version);
            if (!packages.Contains(key)) throw new InvalidDataException($"compile metadata package was not handed off: {key}");
            return Path.Combine(root, RootPath, "packages", key);
        }
        return projects => ScribeMetadataReferenceResolver.DescribeInputPaths(projects, Locate)
            .Concat(RegisteredInputs(projects, record.Assemblies).Select(assembly => Path.Combine(root, MaterialPath(assembly))))
            .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
    }

    private static RegisteredCompileAssembly[] ReadRegistration(RepositorySnapshot snapshot)
    {
        if (!snapshot.TryGetFile(RegistrationPath, out var file)) return [];
        try
        {
            var registration = JsonSerializer.Deserialize<CompileMetadataRegistration>(file.Text, RegistrationOptions);
            if (registration is null || registration.Version != 1)
                throw new InvalidDataException("invalid compile metadata registration version");
            ValidateRegistration(registration.Assemblies);
            return registration.Assemblies;
        }
        catch (JsonException exception)
        {
            throw new InvalidDataException("invalid compile metadata registration", exception);
        }
    }

    private static void ValidateRegistration(RegisteredCompileAssembly[] assemblies)
    {
        if (assemblies is null) throw new InvalidDataException("missing compile metadata assemblies");
        var names = new HashSet<string>(StringComparer.Ordinal);
        var sources = new HashSet<string>(StringComparer.Ordinal);
        foreach (var assembly in assemblies)
        {
            if (assembly is null || string.IsNullOrWhiteSpace(assembly.Assembly))
                throw new InvalidDataException("invalid registered compile assembly");
            if (!names.Add(assembly.Assembly))
                throw new InvalidDataException($"duplicate registered compile assembly: {assembly.Assembly}");
            if (!IsPath(assembly.Source, ".dll") || assembly.Source.StartsWith(RootPath + "/", StringComparison.Ordinal))
                throw new InvalidDataException($"invalid registered compile source: {assembly.Source}");
            if (!sources.Add(assembly.Source))
                throw new InvalidDataException($"duplicate registered compile source: {assembly.Source}");
            if (Path.GetFileName(assembly.Source) != assembly.Assembly + ".dll")
                throw new InvalidDataException($"invalid registered compile assembly source: {assembly.Assembly}");
            if (assembly.Projects is not { Length: > 0 })
                throw new InvalidDataException($"missing registered compile projects: {assembly.Assembly}");
            var projects = new HashSet<string>(StringComparer.Ordinal);
            foreach (var project in assembly.Projects)
            {
                if (!IsPath(project, ".csproj"))
                    throw new InvalidDataException($"invalid registered compile project: {project}");
                if (!projects.Add(project))
                    throw new InvalidDataException($"duplicate registered compile project: {project}");
            }
        }
    }

    private static IEnumerable<RegisteredCompileAssembly> RegisteredInputs(
        IEnumerable<ScribeCompilationProject> projects, RegisteredCompileAssembly[] assemblies)
    {
        foreach (var project in projects)
        {
            var document = XDocument.Load(new StringReader(project.ProjectContent), LoadOptions.None);
            foreach (var reference in document.Descendants().Where(element => element.Name.LocalName == "Reference"))
            {
                if (assemblies.Length == 0)
                    throw new InvalidDataException($"compile metadata registration is missing for {project.Path}");
                var name = (string?)reference.Attribute("Include");
                var assembly = assemblies.SingleOrDefault(item => item.Assembly == name && item.Projects.Contains(project.Path, StringComparer.Ordinal))
                    ?? throw new InvalidDataException($"unregistered compile reference: {project.Path}: {name}");
                yield return assembly;
            }
        }
    }

    private static bool IsPath(string? path, string extension) => path is not null && RepoPath.TryCreate(path, out _)
        && !path.Contains(':', StringComparison.Ordinal) && path.EndsWith(extension, StringComparison.Ordinal);

    private static string MaterialPath(RegisteredCompileAssembly assembly) => RootPath + "/registered/" + assembly.Source;

    private static void RequireMaterial(string root, string source)
    {
        var path = root;
        foreach (var segment in source.Split('/'))
        {
            path = Path.Combine(path, segment);
            if ((!File.Exists(path) && !Directory.Exists(path)) || (File.GetAttributes(path) & FileAttributes.ReparsePoint) != 0)
                throw new InvalidDataException($"registered compile material is unavailable: {source}");
        }
        if (!File.Exists(path)) throw new InvalidDataException($"registered compile material is unavailable: {source}");
    }

    private static string PackageKey(string id, string version) => id.ToLowerInvariant() + "/" + version.ToLowerInvariant();
}
