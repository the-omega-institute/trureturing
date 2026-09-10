using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record BuiltTestProject(string Project, string Assembly);

internal static class CommonBuildOutputs
{
    internal const string RootPath = CommonExecutionEvidence.RootPath + "/build-outputs";
    internal const string TestsPath = RootPath + "/test-assemblies.json";
    internal const string PackagesPath = RootPath + "/packages";

    internal static string[] Collect(string root)
    {
        var projects = new Dictionary<string, string>(StringComparer.Ordinal);
        var paths = new HashSet<string>(StringComparer.Ordinal);
        var snapshot = CommonExecutionEvidence.Snapshot(root);
        foreach (var file in Directory.GetFiles(Path.Combine(root, RootPath), "*.outputs", SearchOption.AllDirectories))
        {
            var lines = File.ReadAllLines(file);
            if (lines.Length < 6 || !lines[4].StartsWith("reference=", StringComparison.Ordinal))
                throw new InvalidDataException("missing compiler output inventory: " + file);
            var project = Relative(lines[0]);
            var assembly = Relative(lines[1]);
            var directory = Path.TrimEndingDirectorySeparator(Path.GetFullPath(lines[2])) + Path.DirectorySeparatorChar;
            var reference = lines[4]["reference=".Length..];
            if (!snapshot.TryGetFile(project, out _) || !projects.TryAdd(project, assembly))
                throw new InvalidDataException("missing or duplicate built project: " + project);
            var outputs = lines.Skip(5).Select(Path.GetFullPath)
                .Where(path => path.StartsWith(directory, StringComparison.Ordinal) || path == reference).Select(Relative).ToArray();
            if (!outputs.Contains(assembly, StringComparer.Ordinal))
                throw new InvalidDataException("compiler did not record its TargetPath: " + assembly);
            if (reference.Length != 0 && !outputs.Contains(Relative(reference), StringComparer.Ordinal))
                throw new InvalidDataException("compiler did not record its reference assembly: " + reference);
            using var stream = File.OpenRead(Path.Combine(root, assembly));
            using var pe = new PEReader(stream);
            var metadata = pe.GetMetadataReader();
            if (metadata.GetString(metadata.GetAssemblyDefinition().Name) != Path.GetFileNameWithoutExtension(assembly))
                throw new InvalidDataException("compiler assembly identity mismatch: " + assembly);
            foreach (var path in outputs)
            {
                if (!File.Exists(Path.Combine(root, path))) throw new InvalidDataException("missing build output: " + path);
                paths.Add(path);
            }
            // NuGet's resolved file inventory also serves tests which compile
            // synthetic projects or query package metadata. Assets themselves
            // contain producer paths and are never used by a recipient.
            using var assets = JsonDocument.Parse(File.ReadAllText(lines[3]));
            var folders = assets.RootElement.GetProperty("packageFolders").EnumerateObject().Select(item => item.Name).ToArray();
            foreach (var library in assets.RootElement.GetProperty("libraries").EnumerateObject())
            {
                if (library.Value.GetProperty("type").GetString() != "package") continue;
                var package = library.Value.GetProperty("path").GetString()!;
                foreach (var entry in library.Value.GetProperty("files").EnumerateArray())
                {
                    var relative = package + "/" + entry.GetString();
                    if (!RepoPath.TryCreate(relative, out _)) throw new InvalidDataException("invalid resolved package file: " + relative);
                    var destination = PackagesPath + "/" + relative;
                    if (!paths.Add(destination)) continue;
                    var source = folders.Select(folder => Path.Combine(folder, relative)).FirstOrDefault(File.Exists)
                        ?? throw new InvalidDataException("missing resolved package file: " + relative);
                    var target = Path.Combine(root, destination);
                    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                    File.Copy(source, target, overwrite: true);
                }
            }
        }
        var selected = EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadSnapshotProjects(snapshot));
        var tests = selected.Select(project => new BuiltTestProject(project, projects.TryGetValue(project, out var assembly)
            ? assembly : throw new InvalidDataException("selected test project was not built: " + project))).ToArray();
        foreach (var assembly in tests.Select(test => test.Assembly).Concat(new[] {
                     CommonExecutionEvidence.CliPath, CommonExecutionEvidence.RunnerPath, CommonExecutionEvidence.ScribePath }))
            foreach (var path in new[] { assembly, Path.ChangeExtension(assembly, ".deps.json"), Path.ChangeExtension(assembly, ".runtimeconfig.json") })
                if (!paths.Contains(path)) throw new InvalidDataException("missing runtime output: " + path);
        CommonExecutionEvidence.Write(root, TestsPath, tests);
        return paths.Append(TestsPath).ToArray();

        string Relative(string path)
        {
            var relative = Path.GetRelativePath(root, Path.GetFullPath(path)).Replace('\\', '/');
            if (!RepoPath.TryCreate(relative, out _)) throw new InvalidDataException("build output escapes candidate: " + path);
            return relative;
        }
    }

    internal static Dictionary<string, string> TestAssemblies(string root, CommonStageRecord build)
    {
        if (!build.Materials.Any(material => material.Path == TestsPath))
            throw new InvalidDataException("build has no test runtime inventory");
        var tests = CommonExecutionEvidence.Read<BuiltTestProject[]>(root, TestsPath);
        foreach (var test in tests)
            if (!build.Materials.Any(material => material.Path == test.Assembly))
                throw new InvalidDataException("unbound test runtime: " + test.Project);
        return tests.ToDictionary(test => test.Project, test => test.Assembly, StringComparer.Ordinal);
    }
}
