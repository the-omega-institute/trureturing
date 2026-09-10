using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record BuiltTestProject(string Project, string Assembly);

internal static partial class CommonBuildOutputs
{
    internal const string RootPath = CommonExecutionEvidence.RootPath + "/build-outputs";
    internal const string TestsPath = RootPath + "/test-assemblies.json";
    internal const string PackagesPath = RootPath + "/packages";

    internal static string[] Collect(string root)
    {
        var projects = new Dictionary<string, BuiltProject>(StringComparer.Ordinal);
        var paths = new HashSet<string>(StringComparer.Ordinal);
        var snapshot = CommonExecutionEvidence.Snapshot(root);
        foreach (var file in Directory.GetFiles(Path.Combine(root, RootPath), "*.outputs", SearchOption.AllDirectories))
        {
            var lines = File.ReadAllLines(file);
            if (lines.Length < 7 || !lines[4].StartsWith("reference=", StringComparison.Ordinal) || lines[5] != "native-inputs=1")
                throw new InvalidDataException("missing compiler output inventory: " + file);
            var project = Relative(lines[0]);
            var assembly = Relative(lines[1]);
            var directory = Path.TrimEndingDirectorySeparator(Path.GetFullPath(lines[2])) + Path.DirectorySeparatorChar;
            var reference = lines[4]["reference=".Length..];
            var entries = lines.Skip(6).ToArray();
            var references = entries.Where(line => line.StartsWith("project=", StringComparison.Ordinal)).Select(line => Relative(line[8..])).ToArray();
            var inputs = entries.Where(line => line.StartsWith("input=", StringComparison.Ordinal)).Select(line => Path.GetFullPath(line[6..])).ToArray();
            var outputs = entries.Where(line => !line.StartsWith("project=", StringComparison.Ordinal) && !line.StartsWith("input=", StringComparison.Ordinal)).Select(Path.GetFullPath)
                .Where(path => path.StartsWith(directory, StringComparison.Ordinal) || path == reference).Select(Relative).ToArray();
            if (!snapshot.TryGetFile(project, out _) || !projects.TryAdd(project, new(assembly, lines[3], references, inputs, outputs)))
                throw new InvalidDataException("missing or duplicate built project: " + project);
            if (!outputs.Contains(assembly, StringComparer.Ordinal))
                throw new InvalidDataException("compiler did not record its TargetPath: " + assembly);
            if (reference.Length != 0 && !outputs.Contains(Relative(reference), StringComparer.Ordinal))
                throw new InvalidDataException("compiler did not record its reference assembly: " + reference);
        }
        var selected = EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadSnapshotProjects(snapshot));
        var tests = selected.Select(project => new BuiltTestProject(project, projects.TryGetValue(project, out var built)
            ? built.Assembly : throw new InvalidDataException("selected test project was not built: " + project))).ToArray();
        var required = new[] { CommonExecutionEvidence.CliPath, CommonExecutionEvidence.RunnerPath, CommonExecutionEvidence.ScribePath };
        var pending = new Queue<string>(selected.Concat(projects.Where(pair => required.Contains(pair.Value.Assembly, StringComparer.Ordinal)).Select(pair => pair.Key)));
        var retained = new HashSet<string>(StringComparer.Ordinal);
        while (pending.TryDequeue(out var project))
        {
            if (!retained.Add(project)) continue;
            if (!projects.TryGetValue(project, out var built)) throw new InvalidDataException("required project was not built: " + project);
            foreach (var dependency in built.References) pending.Enqueue(dependency);
            using var stream = File.OpenRead(Path.Combine(root, built.Assembly));
            using var pe = new PEReader(stream);
            var metadata = pe.GetMetadataReader();
            if (metadata.GetString(metadata.GetAssemblyDefinition().Name) != Path.GetFileNameWithoutExtension(built.Assembly))
                throw new InvalidDataException("compiler assembly identity mismatch: " + built.Assembly);
            foreach (var path in built.Outputs)
            {
                if (!File.Exists(Path.Combine(root, path))) throw new InvalidDataException("missing build output: " + path);
                paths.Add(path);
            }
        }
        paths.UnionWith(CollectPackages(root, projects.Values, retained.Select(project => projects[project]), snapshot));
        foreach (var assembly in tests.Select(test => test.Assembly).Concat(required))
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

    private sealed record BuiltProject(string Assembly, string Assets, string[] References, string[] Inputs, string[] Outputs);

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
