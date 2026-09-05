using System.Text;
using System.Xml.Linq;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal static class ControllerClosure
{
    private const string EntryProject =
        "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj";
    internal static IReadOnlyList<string> RuntimePaths { get; } =
    [
        "tools/scripts/report/report-supervisor.sh",
    ];

    internal static IReadOnlyList<string> Derive(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        var tracked = snapshot.Files.Values
            .Select(static file => file.Path.Value)
            .ToHashSet(StringComparer.Ordinal);
        return DeriveCore(tracked, project => snapshot.TryGetFile(project, out var file)
            ? file.Text
            : throw new InvalidDataException("controller project reference is absent from base"));
    }

    private static IReadOnlyList<string> DeriveCore(
        IReadOnlySet<string> tracked,
        Func<string, string> readProjectText)
    {
        ArgumentNullException.ThrowIfNull(tracked);
        ArgumentNullException.ThrowIfNull(readProjectText);
        var projects = ProjectClosure(readProjectText, tracked);
        var evaluator = new HashSet<string>(StringComparer.Ordinal);
        foreach (var project in projects)
        {
            evaluator.Add(project);
            var directory = ProjectDirectory(project);
            evaluator.UnionWith(tracked.Where(path =>
                path.StartsWith(directory + "/", StringComparison.Ordinal)
                && path.EndsWith(".cs", StringComparison.Ordinal)
                && !path.Contains("/bin/", StringComparison.Ordinal)
                && !path.Contains("/obj/", StringComparison.Ordinal)));
            var lockFile = directory + "/packages.lock.json";
            if (tracked.Contains(lockFile)) evaluator.Add(lockFile);
            AddProjectInputs(readProjectText, project, evaluator, tracked);
        }

        AddIfTracked(evaluator, tracked, "Directory.Build.props");
        AddIfTracked(evaluator, tracked, "Directory.Packages.props");
        foreach (var path in RuntimePaths) AddIfTracked(evaluator, tracked, path);

        return evaluator.Order(StringComparer.Ordinal).ToArray();
    }

    private static HashSet<string> ProjectClosure(
        Func<string, string> readProjectText,
        IReadOnlySet<string> tracked)
    {
        var pending = new Stack<string>();
        var projects = new HashSet<string>(StringComparer.Ordinal);
        pending.Push(EntryProject);
        while (pending.TryPop(out var project))
        {
            if (!tracked.Contains(project) || !projects.Add(project))
            {
                if (!tracked.Contains(project))
                    throw new InvalidDataException("controller project reference is absent from base");
                continue;
            }
            var document = ReadProject(readProjectText, project);
            foreach (var reference in document.Descendants()
                         .Where(static element => element.Name.LocalName == "ProjectReference"))
            {
                pending.Push(ResolveProjectPath(project, RequiredLiteralInclude(reference)));
            }
        }
        return projects;
    }

    private static void AddProjectInputs(
        Func<string, string> readProjectText,
        string project,
        HashSet<string> evaluator,
        IReadOnlySet<string> tracked)
    {
        var document = ReadProject(readProjectText, project);
        foreach (var input in document.Descendants().Where(static element =>
                     element.Name.LocalName is "AdditionalFiles" or "Compile"))
        {
            var include = input.Attribute("Include")?.Value;
            if (include is null) continue;
            if (include.Contains('*', StringComparison.Ordinal)
                || include.Contains('?', StringComparison.Ordinal)
                || include.Contains("$(", StringComparison.Ordinal))
            {
                throw new InvalidDataException("controller project input is not a literal path");
            }
            var path = ResolveProjectPath(project, include);
            if (!tracked.Contains(path))
                throw new InvalidDataException("controller project input is absent from base");
            evaluator.Add(path);
        }
    }

    private static XDocument ReadProject(Func<string, string> readProjectText, string project)
    {
        try
        {
            return XDocument.Parse(readProjectText(project), LoadOptions.None);
        }
        catch (Exception exception) when (exception is DecoderFallbackException or System.Xml.XmlException)
        {
            throw new InvalidDataException("controller project is invalid", exception);
        }
    }

    private static string RequiredLiteralInclude(XElement element)
    {
        var include = element.Attribute("Include")?.Value;
        if (string.IsNullOrEmpty(include)
            || include.Contains('*', StringComparison.Ordinal)
            || include.Contains('?', StringComparison.Ordinal)
            || include.Contains("$(", StringComparison.Ordinal))
        {
            throw new InvalidDataException("controller project reference is not a literal path");
        }
        return include;
    }

    private static string ResolveProjectPath(string project, string include)
    {
        var directory = ProjectDirectory(project).Split('/').ToList();
        foreach (var segment in include.Replace('\\', '/').Split('/'))
        {
            if (segment is "" or ".") continue;
            if (segment == "..")
            {
                if (directory.Count == 0)
                    throw new InvalidDataException("controller project input escapes the repository");
                directory.RemoveAt(directory.Count - 1);
            }
            else
            {
                directory.Add(segment);
            }
        }
        var path = string.Join('/', directory);
        EnsureCanonical(path);
        return path;
    }

    private static string ProjectDirectory(string project) =>
        project[..project.LastIndexOf('/')];

    private static void AddIfTracked(
        HashSet<string> paths,
        IReadOnlySet<string> tracked,
        string path)
    {
        if (!tracked.Contains(path))
            throw new InvalidDataException(
                $"controller runtime dependency is absent from base: {path}");
        paths.Add(path);
    }

    private static void EnsureCanonical(string path)
    {
        if (path.Length == 0
            || path.StartsWith("/", StringComparison.Ordinal)
            || path.Contains('\\', StringComparison.Ordinal)
            || path.Split('/').Any(static segment => segment is "" or "." or ".."))
        {
            throw new InvalidDataException("controller path is not canonical");
        }
    }
}
