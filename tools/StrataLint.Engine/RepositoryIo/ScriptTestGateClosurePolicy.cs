using System.Collections.Immutable;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal sealed record ScriptTestGateClosure(
    ImmutableArray<string> ExactPaths,
    ImmutableArray<string> DirectoryPrefixes)
{
    internal bool Covers(string path) => ExactPaths.Contains(path, StringComparer.Ordinal)
        || DirectoryPrefixes.Any(prefix =>
            path.StartsWith(prefix + "/", StringComparison.Ordinal));
}

internal sealed record ScriptTestProjectClosure(
    IReadOnlyList<string> Projects,
    IReadOnlyList<string> DirectoryPrefixes,
    IReadOnlySet<string> TrackedPaths);

internal static class ScriptTestGateClosurePolicy
{
    internal const string ProjectPath =
        "tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj";

    private static readonly IReadOnlyList<string> AncestorBuildFileNames =
    [
        "Directory.Build.props",
        "Directory.Packages.props",
        "global.json",
        ".editorconfig",
        "NuGet.Config",
    ];

    internal static ScriptTestGateClosure Derive(
        RepositorySnapshot snapshot,
        IReadOnlyCollection<string> controllerInputs)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(controllerInputs);

        var projectClosure = DeriveProjects(snapshot);
        var exact = new HashSet<string>(projectClosure.Projects, StringComparer.Ordinal);
        foreach (var project in projectClosure.Projects)
        {
            var lockFile = ProjectDirectory(project) + "/packages.lock.json";
            RequireTracked(projectClosure.TrackedPaths, lockFile, "project lock file");
            exact.Add(lockFile);
        }

        foreach (var directory in projectClosure.DirectoryPrefixes)
        {
            AddAncestorBuildInputs(directory, projectClosure.TrackedPaths, exact);
        }

        foreach (var input in controllerInputs)
        {
            EnsureCanonical(input, "controller input");
            RequireTracked(projectClosure.TrackedPaths, input, "controller input");
            exact.Add(input);
        }

        foreach (var input in ScriptTestInputDeriver.Derive(snapshot, projectClosure))
        {
            RequireTracked(projectClosure.TrackedPaths, input.Path, $"consumed path for {input.Identity}");
            exact.Add(input.Path);
        }

        return new ScriptTestGateClosure(
            exact.Order(StringComparer.Ordinal).ToImmutableArray(),
            projectClosure.DirectoryPrefixes.Order(StringComparer.Ordinal).ToImmutableArray());
    }

    private static ScriptTestProjectClosure DeriveProjects(RepositorySnapshot snapshot)
    {
        var tracked = snapshot.Files.Values
            .Select(static file => file.Path.Value)
            .ToHashSet(StringComparer.Ordinal);
        var projects = new HashSet<string>(StringComparer.Ordinal);
        var pending = new Stack<string>();
        pending.Push(ProjectPath);
        while (pending.TryPop(out var project))
        {
            EnsureCanonical(project, "project path");
            RequireTracked(tracked, project, "project reference");
            if (!projects.Add(project)) continue;

            var document = ReadProject(snapshot, project);
            foreach (var reference in document.Descendants()
                         .Where(static element => element.Name.LocalName == "ProjectReference"))
            {
                pending.Push(ResolveProjectPath(project, RequireLiteralReference(reference, project)));
            }
        }

        var directories = projects
            .Select(ProjectDirectory)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        return new ScriptTestProjectClosure(
            projects.Order(StringComparer.Ordinal).ToArray(),
            directories,
            tracked);
    }

    private static XDocument ReadProject(RepositorySnapshot snapshot, string project)
    {
        try
        {
            if (!snapshot.TryGetFile(project, out var file))
                throw new InvalidDataException($"ScriptTests gate project is absent: {project}");
            return XDocument.Parse(file.Text, LoadOptions.None);
        }
        catch (System.Xml.XmlException exception)
        {
            throw new InvalidDataException($"ScriptTests gate project is invalid: {project}", exception);
        }
    }

    private static string RequireLiteralReference(XElement reference, string project)
    {
        var include = reference.Attribute("Include")?.Value;
        if (string.IsNullOrWhiteSpace(include)
            || include.Contains('*', StringComparison.Ordinal)
            || include.Contains('?', StringComparison.Ordinal)
            || include.Contains("$(", StringComparison.Ordinal))
        {
            throw new InvalidDataException(
                $"ScriptTests gate project reference is unresolved in {project}");
        }
        return include;
    }

    private static void AddAncestorBuildInputs(
        string directory,
        IReadOnlySet<string> tracked,
        ISet<string> exact)
    {
        for (var current = directory; ; current = ParentDirectory(current))
        {
            foreach (var fileName in AncestorBuildFileNames)
            {
                var candidate = current.Length == 0 ? fileName : current + "/" + fileName;
                if (tracked.Contains(candidate)) exact.Add(candidate);
            }
            if (current.Length == 0) break;
        }
    }

    private static string ResolveProjectPath(string project, string include)
    {
        var segments = ProjectDirectory(project).Split('/').ToList();
        foreach (var segment in include.Replace('\\', '/').Split('/'))
        {
            if (segment is "" or ".") continue;
            if (segment == "..")
            {
                if (segments.Count == 0)
                    throw new InvalidDataException(
                        $"ScriptTests gate project reference escapes the repository: {project}");
                segments.RemoveAt(segments.Count - 1);
                continue;
            }
            segments.Add(segment);
        }
        var result = string.Join('/', segments);
        EnsureCanonical(result, "project reference");
        return result;
    }

    private static string ProjectDirectory(string project) =>
        project[..project.LastIndexOf('/')];

    private static string ParentDirectory(string directory) =>
        directory.LastIndexOf('/') is var slash && slash >= 0 ? directory[..slash] : string.Empty;

    private static void RequireTracked(
        IReadOnlySet<string> tracked,
        string path,
        string role)
    {
        if (!tracked.Contains(path))
            throw new InvalidDataException($"ScriptTests gate {role} is absent: {path}");
    }

    private static void EnsureCanonical(string path, string role)
    {
        if (path.Length == 0
            || path.StartsWith("/", StringComparison.Ordinal)
            || path.Contains('\\', StringComparison.Ordinal)
            || path.Split('/').Any(static segment => segment is "" or "." or ".."))
        {
            throw new InvalidDataException($"ScriptTests gate {role} is not canonical: {path}");
        }
    }
}
