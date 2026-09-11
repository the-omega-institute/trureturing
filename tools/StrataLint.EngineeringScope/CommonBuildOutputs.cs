using System.Reflection.Metadata;
using System.Reflection.PortableExecutable;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record BuiltTestProject(string Project, string Assembly);

internal static class CommonBuildOutputs
{
    internal const string RootPath = CommonExecutionEvidence.RootPath + "/build-outputs";
    internal const string TestsPath = RootPath + "/test-assemblies.json";
    internal const string PackagesPath = RootPath + "/packages";

    internal static string[] Collect(string root) => Collect(root, null);

    // When a resource plan supplies roots, only those roots and their explicitly
    // registered references are admitted. A null root set retains the complete
    // engineering entrypoint for callers that explicitly request it.
    internal static string[] Collect(string root, IEnumerable<string>? selectedRoots)
    {
        var projects = new Dictionary<string, string>(StringComparer.Ordinal);
        var paths = new HashSet<string>(StringComparer.Ordinal);
        string? packageRoot = null;
        var snapshot = CommonExecutionEvidence.Snapshot(root);
        var registrations = EngineeringProjectRegistry.Read(snapshot);
        var selected = selectedRoots is null ? null : RegisteredClosure(registrations, selectedRoots);
        foreach (var registration in registrations.Projects.Where(project => project.Role != "compile-fail-proof"
                     && (selected is null || selected.Contains(project.Path))))
        {
            var file = Path.Combine(root, RootPath, registration.Path + ".outputs");
            if (!File.Exists(file))
                throw new InvalidDataException("missing registered build receipt: " + registration.Path);
            var lines = File.ReadAllLines(file);
            if (lines.Length < 6 || !lines[3].StartsWith("packages=", StringComparison.Ordinal)
                || !lines[4].StartsWith("reference=", StringComparison.Ordinal))
                throw new InvalidDataException("missing compiler output inventory: " + file);
            var project = Relative(lines[0]);
            if (project != registration.Path)
                throw new InvalidDataException($"build receipt project mismatch: expected {registration.Path}, received {project}");
            var configuredRoot = lines[3]["packages=".Length..];
            if (string.IsNullOrWhiteSpace(configuredRoot) || !Path.IsPathFullyQualified(configuredRoot))
                throw new InvalidDataException("missing absolute NuGetPackageRoot in compiler output receipt: " + file);
            configuredRoot = Path.TrimEndingDirectorySeparator(Path.GetFullPath(configuredRoot));
            if (packageRoot is not null && packageRoot != configuredRoot)
                throw new InvalidDataException("conflicting NuGetPackageRoot in compiler output receipt: " + file);
            packageRoot = configuredRoot;
            var assembly = Relative(lines[1]);
            var directory = Path.TrimEndingDirectorySeparator(Path.GetFullPath(lines[2])) + Path.DirectorySeparatorChar;
            var reference = lines[4]["reference=".Length..];
            projects.Add(project, assembly);
            var outputs = lines.Skip(5).Select(Path.GetFullPath)
                .Where(path => path.StartsWith(directory, StringComparison.Ordinal) || path == reference).Select(Relative).ToArray();
            if (!outputs.Contains(assembly, StringComparer.Ordinal))
                throw new InvalidDataException("compiler did not record its TargetPath: " + assembly);
            if (reference.Length != 0 && !outputs.Contains(Relative(reference), StringComparer.Ordinal))
                throw new InvalidDataException("compiler did not record its reference assembly: " + reference);
            using var stream = File.OpenRead(Path.Combine(root, assembly));
            using var pe = new PEReader(stream);
            var metadata = pe.GetMetadataReader();
            if (metadata.GetString(metadata.GetAssemblyDefinition().Name) != registration.Assembly)
                throw new InvalidDataException($"compiler assembly identity mismatch: {project}: expected {registration.Assembly}: {assembly}");
            foreach (var path in outputs)
            {
                if (!File.Exists(Path.Combine(root, path))) throw new InvalidDataException("missing build output: " + path);
                paths.Add(path);
            }
        }
        var needsTestPackages = registrations.Projects.Any(project => project.IsTest
            && (selected is null || selected.Contains(project.Path)));
        foreach (var material in needsTestPackages ? PackageMaterialRegistry.Expand(root, packageRoot
                     ?? throw new InvalidDataException("missing compiler NuGetPackageRoot receipt")) : [])
        {
            var destination = PackagesPath + "/" + material.Relative;
            paths.Add(destination);
            var target = Path.Combine(root, destination);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(material.Source, target, overwrite: true);
        }
        var testProjects = EngineeringTestPlanPolicy.Evaluate(RepositoryRules.ReadSnapshotProjects(snapshot))
            .Where(project => selected is null || selected.Contains(project)).ToArray();
        var tests = testProjects.Select(project => new BuiltTestProject(project, projects.TryGetValue(project, out var assembly)
            ? assembly : throw new InvalidDataException("selected test project was not built: " + project))).ToArray();
        var runtime = selected is null ? new[] {
            CommonExecutionEvidence.CliPath, CommonExecutionEvidence.RunnerPath,
            CommonExecutionEvidence.LeanProducerPath, CommonExecutionEvidence.ScribePath }
            : selectedRoots!.Select(project => projects[project]).ToArray();
        foreach (var assembly in tests.Select(test => test.Assembly).Concat(runtime))
            foreach (var path in new[] { assembly, Path.ChangeExtension(assembly, ".deps.json"), Path.ChangeExtension(assembly, ".runtimeconfig.json") })
                if (!paths.Contains(path)) throw new InvalidDataException("missing runtime output: " + path);
        CommonExecutionEvidence.Write(root, TestsPath, tests);
        return paths.Append(TestsPath).Order(StringComparer.Ordinal).ToArray();

        string Relative(string path)
        {
            var relative = Path.GetRelativePath(root, Path.GetFullPath(path)).Replace('\\', '/');
            if (!RepoPath.TryCreate(relative, out _)) throw new InvalidDataException("build output escapes candidate: " + path);
            return relative;
        }
    }

    private static HashSet<string> RegisteredClosure(EngineeringProjectRegistry registry, IEnumerable<string> roots)
    {
        var byPath = registry.Projects.ToDictionary(project => project.Path, StringComparer.Ordinal);
        var result = new HashSet<string>(StringComparer.Ordinal);
        void Visit(string path)
        {
            if (!byPath.TryGetValue(path, out var project)) throw new InvalidDataException("unregistered requested build root: " + path);
            if (!result.Add(path)) return;
            foreach (var reference in project.References) Visit(reference);
        }
        foreach (var root in roots) Visit(root);
        return result;
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
