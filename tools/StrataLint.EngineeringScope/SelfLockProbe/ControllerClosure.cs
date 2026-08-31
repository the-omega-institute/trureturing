using System.Collections.Concurrent;
using System.Formats.Tar;
using System.Text;
using System.Xml.Linq;

namespace StrataLint.EngineeringScope.SelfLockProbe;

internal sealed record ControllerClosureSnapshot(
    string Commit,
    IReadOnlyList<string> EvaluatorPaths,
    IReadOnlySet<string> OwnerPaths);

internal static class ControllerClosure
{
    internal const string ProducerPath =
        "tools/StrataLint.EngineeringScope/SelfLockProbe/StrictArtifacts.cs";
    private const string EntryProject =
        "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj";
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    private static readonly ConcurrentDictionary<(string Root, string Commit), ControllerClosureSnapshot>
        Cache = new();

    internal static ControllerClosureSnapshot Derive(string controllerRoot)
    {
        var root = ProcessTools.RequireRepositoryRoot(controllerRoot);
        var commit = ProcessTools.GitText(root, "rev-parse", "HEAD");
        return Cache.GetOrAdd((root, commit), static key => DeriveCore(key.Root, key.Commit));
    }

    internal static byte[] ReadAtHead(string controllerRoot, string relativePath)
    {
        EnsureCanonical(relativePath);
        var output = ProcessTools.Run(
            "/usr/bin/git",
            ["-C", controllerRoot, "show", $"HEAD:{relativePath}"],
            controllerRoot);
        if (output.ExitCode != 0 || output.StandardError.Length != 0)
        {
            throw new InvalidDataException("controller source is absent from base");
        }
        return output.StandardOutput;
    }

    internal static IReadOnlyDictionary<string, byte[]> ReadAtHead(
        string controllerRoot,
        IReadOnlyList<string> relativePaths)
    {
        if (relativePaths.Count == 0)
            throw new InvalidDataException("controller closure is empty");
        foreach (var path in relativePaths) EnsureCanonical(path);
        var output = ProcessTools.Run(
            "/usr/bin/git",
            ["-C", controllerRoot, "archive", "--format=tar", "HEAD", "--", .. relativePaths],
            controllerRoot);
        if (output.ExitCode != 0 || output.StandardError.Length != 0)
            throw new InvalidDataException("controller closure archive failed");

        var files = new Dictionary<string, byte[]>(StringComparer.Ordinal);
        using var stream = new MemoryStream(output.StandardOutput, writable: false);
        using var archive = new TarReader(stream);
        while (archive.GetNextEntry() is { } entry)
        {
            if (entry.EntryType is not (TarEntryType.RegularFile or TarEntryType.V7RegularFile)
                || entry.DataStream is null)
            {
                continue;
            }
            using var content = new MemoryStream();
            entry.DataStream.CopyTo(content);
            files.Add(entry.Name, content.ToArray());
        }
        if (files.Count != relativePaths.Count
            || relativePaths.Any(path => !files.ContainsKey(path)))
        {
            throw new InvalidDataException("controller closure archive is incomplete");
        }
        return files;
    }

    private static ControllerClosureSnapshot DeriveCore(string root, string commit)
    {
        var tracked = TrackedPaths(root);
        var projects = ProjectClosure(root, tracked);
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
            AddProjectInputs(root, project, evaluator, tracked);
        }

        AddIfTracked(evaluator, tracked, "Directory.Build.props");
        AddIfTracked(evaluator, tracked, "Directory.Packages.props");
        AddIfTracked(evaluator, tracked, "tools/scripts/workflow/pure-revert-detect.sh");
        AddIfTracked(evaluator, tracked, "tools/scripts/workflow/self-lock-probe.sh");
        AddIfTracked(evaluator, tracked, "tools/scripts/report/report-supervisor.sh");

        var owners = new HashSet<string>(evaluator, StringComparer.Ordinal);
        owners.Add("tools/self-lock-probe-result.json");
        owners.Add(".github/workflows/ci.yml");
        owners.UnionWith(tracked.Where(static path => path.StartsWith(
            "tools/tests/StrataLint.ScriptTests/SelfLockProbeScriptTests.",
            StringComparison.Ordinal)));
        return new ControllerClosureSnapshot(
            commit,
            evaluator.Order(StringComparer.Ordinal).ToArray(),
            owners);
    }

    private static HashSet<string> TrackedPaths(string root)
    {
        var output = ProcessTools.Run(
            "/usr/bin/git",
            ["-C", root, "ls-tree", "-r", "--name-only", "-z", "HEAD"],
            root);
        if (output.ExitCode != 0 || output.StandardError.Length != 0)
        {
            throw new InvalidDataException("controller tree enumeration failed");
        }
        var result = new HashSet<string>(StringComparer.Ordinal);
        foreach (var bytes in SplitNul(output.StandardOutput))
        {
            string path;
            try
            {
                path = StrictUtf8.GetString(bytes);
            }
            catch (DecoderFallbackException exception)
            {
                throw new InvalidDataException("controller path is not strict UTF-8", exception);
            }
            EnsureCanonical(path);
            result.Add(path);
        }
        return result;
    }

    private static HashSet<string> ProjectClosure(string root, IReadOnlySet<string> tracked)
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
            var document = ReadProject(root, project);
            foreach (var reference in document.Descendants()
                         .Where(static element => element.Name.LocalName == "ProjectReference"))
            {
                pending.Push(ResolveProjectPath(project, RequiredLiteralInclude(reference)));
            }
        }
        return projects;
    }

    private static void AddProjectInputs(
        string root,
        string project,
        HashSet<string> evaluator,
        IReadOnlySet<string> tracked)
    {
        var document = ReadProject(root, project);
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

    private static XDocument ReadProject(string root, string project)
    {
        try
        {
            return XDocument.Parse(StrictUtf8.GetString(ReadAtHead(root, project)), LoadOptions.None);
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
            throw new InvalidDataException("controller runtime dependency is absent from base");
        paths.Add(path);
    }

    private static IEnumerable<byte[]> SplitNul(byte[] bytes)
    {
        var start = 0;
        for (var index = 0; index < bytes.Length; index++)
        {
            if (bytes[index] != 0) continue;
            if (index == start) throw new InvalidDataException("controller path record is empty");
            yield return bytes[start..index];
            start = index + 1;
        }
        if (start != bytes.Length)
            throw new InvalidDataException("controller path record is partial");
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
