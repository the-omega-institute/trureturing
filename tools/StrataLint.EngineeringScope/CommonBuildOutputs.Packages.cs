using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static partial class CommonBuildOutputs
{
    private static string[] CollectPackages(string root, IEnumerable<BuiltProject> projects,
        IEnumerable<BuiltProject> retained, RepositorySnapshot snapshot)
    {
        var packages = new Dictionary<string, PackageFiles>(StringComparer.OrdinalIgnoreCase);
        var documents = new Dictionary<string, JsonDocument>(StringComparer.Ordinal);
        try
        {
            foreach (var project in projects)
            {
                var document = JsonDocument.Parse(File.ReadAllText(project.Assets));
                documents.Add(project.Assets, document);
                var assets = document.RootElement;
                var folders = assets.GetProperty("packageFolders").EnumerateObject().Select(item => item.Name).ToArray();
                foreach (var library in assets.GetProperty("libraries").EnumerateObject())
                {
                    if (library.Value.GetProperty("type").GetString() != "package") continue;
                    var path = library.Value.GetProperty("path").GetString()!;
                    var files = library.Value.GetProperty("files").EnumerateArray().Select(item => item.GetString()!).ToHashSet(StringComparer.Ordinal);
                    // NuGet's version-folder protocol names the content hash
                    // <lowercase-id>.<normalized-version>.nupkg.sha512.
                    var hash = path.Replace('/', '.') + ".nupkg.sha512";
                    if (!packages.TryGetValue(library.Name, out var package))
                        packages.Add(library.Name, package = new(path, files, hash));
                    else if (path != package.Path || hash != package.HashPath || !files.SetEquals(package.Files))
                        throw new InvalidDataException("inconsistent resolved package inventory: " + library.Name);
                    package.Folders.UnionWith(folders);
                }
            }
            foreach (var project in retained)
            {
                var assets = documents[project.Assets].RootElement;
                // Union every resolved TFM/RID target. NuGet owns RID fallback;
                // choosing only the producer host RID would lose portable consumers.
                foreach (var target in assets.GetProperty("targets").EnumerateObject())
                    foreach (var library in target.Value.EnumerateObject())
                    {
                        if (library.Value.GetProperty("type").GetString() == "project") continue;
                        if (!packages.TryGetValue(library.Name, out var package))
                            throw new InvalidDataException("unresolved target package: " + library.Name);
                        package.Used = true;
                        foreach (var group in library.Value.EnumerateObject())
                        {
                            switch (group.Name)
                            {
                                case "type": case "frameworkAssemblies": break;
                                case "dependencies":
                                    foreach (var dependency in group.Value.EnumerateObject())
                                    {
                                        var resolved = target.Value.EnumerateObject().Where(item =>
                                            item.Name[..item.Name.LastIndexOf('/')].Equals(dependency.Name, StringComparison.OrdinalIgnoreCase)).ToArray();
                                        if (resolved.Length != 1) throw new InvalidDataException("unresolved package dependency: " + dependency.Name);
                                        if (resolved[0].Value.GetProperty("type").GetString() == "package")
                                            package.Dependencies.Add(resolved[0].Name);
                                    }
                                    break;
                                case "compile": case "runtime": case "native": case "resource": case "runtimeTargets":
                                    foreach (var asset in group.Value.EnumerateObject()) package.Include(asset.Name);
                                    break;
                                default:
                                    // Build/content/analyzer inputs can load arbitrary sibling files.
                                    // Unknown native groups have the same conservative boundary.
                                    package.Whole = true;
                                    break;
                            }
                        }
                    }
                foreach (var input in project.Inputs)
                {
                    if (!File.Exists(input)) throw new InvalidDataException("missing evaluated build input: " + input);
                    foreach (var package in packages.Values.Where(package => package.Owns(input)))
                    {
                        package.Used = true;
                        package.Whole = true;
                    }
                }
                var depsPath = System.IO.Path.ChangeExtension(project.Assembly, ".deps.json");
                if (!project.Outputs.Contains(depsPath, StringComparer.Ordinal)) continue;
                using var deps = JsonDocument.Parse(File.ReadAllText(System.IO.Path.Combine(root, depsPath)));
                var definitions = deps.RootElement.GetProperty("libraries");
                foreach (var target in deps.RootElement.GetProperty("targets").EnumerateObject())
                    foreach (var library in target.Value.EnumerateObject())
                    {
                        var definition = definitions.GetProperty(library.Name);
                        if (definition.GetProperty("type").GetString() != "package") continue;
                        if (!packages.TryGetValue(library.Name, out var package)
                            || definition.GetProperty("path").GetString() != package.Path)
                            throw new InvalidDataException("unresolved runtime package: " + library.Name);
                        package.Used = true;
                        package.Include(definition.GetProperty("hashPath").GetString()!);
                        foreach (var group in library.Value.EnumerateObject())
                        {
                            if (group.Name == "dependencies") continue; // The resolved assets graph owns these edges.
                            if (group.Name is "runtime" or "native" or "resources" or "runtimeTargets")
                                foreach (var asset in group.Value.EnumerateObject()) package.Include(asset.Name);
                            else package.Whole = true;
                        }
                    }
            }
            // Tasks/generators can use their resolved dependencies as well as siblings.
            var pending = new Queue<PackageFiles>(packages.Values.Where(package => package.Whole));
            while (pending.TryDequeue(out var package))
                foreach (var name in package.Dependencies)
                {
                    var dependency = packages[name];
                    if (dependency.Whole) continue;
                    dependency.Used = dependency.Whole = true;
                    pending.Enqueue(dependency);
                }
            var metadataPackages = new HashSet<PackageFiles>();
            string Locate(string id, string version)
            {
                if (!packages.TryGetValue(id + "/" + version, out var package))
                    throw new InvalidDataException($"compiler metadata has no resolved package inventory: {id}/{version}");
                package.Used = true;
                metadataPackages.Add(package);
                return package.Folders.Select(folder => Path.Combine(folder, package.Path)).First(Directory.Exists);
            }
            foreach (var input in CommonCompileMetadata.DescribeInputs(snapshot, Locate))
                foreach (var package in metadataPackages.Where(package => package.Owns(input)))
                    package.Include(package.Relative(input));

            var paths = new HashSet<string>(StringComparer.Ordinal);
            foreach (var (name, package) in packages.Where(pair => pair.Value.Used))
            {
                // NuGet's extraction marker, nuspec and content hash are semantic
                // restore/probing inputs; never replace them with a second registry.
                package.Include(name[..name.LastIndexOf('/')].ToLowerInvariant() + ".nuspec");
                package.Include(package.HashPath);
                package.Include(".nupkg.metadata");
                if (package.Files.Contains(".signature.p7s")) package.Include(".signature.p7s");
                foreach (var file in package.Whole ? package.Files : package.Selected)
                {
                    var relative = package.Path + "/" + file;
                    if (!RepoPath.TryCreate(relative, out _)) throw new InvalidDataException("invalid resolved package file: " + relative);
                    var source = package.Folders.Select(folder => Path.Combine(folder, relative)).FirstOrDefault(File.Exists)
                        ?? throw new InvalidDataException("missing resolved package file: " + relative);
                    var destination = PackagesPath + "/" + relative;
                    var target = Path.Combine(root, destination);
                    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                    File.Copy(source, target, overwrite: true);
                    paths.Add(destination);
                }
            }
            return paths.ToArray();
        }
        finally { foreach (var document in documents.Values) document.Dispose(); }
    }

    private sealed class PackageFiles(string path, HashSet<string> files, string hashPath)
    {
        internal string Path { get; } = path;
        internal string HashPath { get; } = hashPath;
        internal HashSet<string> Files { get; } = files;
        internal HashSet<string> Folders { get; } = new(StringComparer.Ordinal);
        internal HashSet<string> Selected { get; } = new(StringComparer.Ordinal);
        internal HashSet<string> Dependencies { get; } = new(StringComparer.OrdinalIgnoreCase);
        internal bool Used { get; set; }
        internal bool Whole { get; set; }
        internal bool Owns(string input) => Folders.Any(folder => input.StartsWith(
            System.IO.Path.Combine(folder, Path) + System.IO.Path.DirectorySeparatorChar, StringComparison.Ordinal));
        internal string Relative(string input) => Folders.Where(folder => input.StartsWith(
                System.IO.Path.Combine(folder, Path) + System.IO.Path.DirectorySeparatorChar, StringComparison.Ordinal))
            .Select(folder => System.IO.Path.GetRelativePath(System.IO.Path.Combine(folder, Path), input).Replace('\\', '/')).First();
        internal void Include(string file)
        {
            // NuGet uses _._ to declare an empty asset group, including virtual
            // placeholders which are not members of the extracted package.
            if (file == "_._" || file.EndsWith("/_._", StringComparison.Ordinal)) return;
            if (!Files.Contains(file)) throw new InvalidDataException("asset is absent from resolved package inventory: " + Path + "/" + file);
            Selected.Add(file);
        }
    }
}
