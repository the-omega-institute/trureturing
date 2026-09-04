using System.Formats.Tar;
using System.Text;
using System.Xml.Linq;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record ControllerClosureSnapshot(
    string Commit,
    IReadOnlyList<string> EvaluatorPaths,
    IReadOnlySet<string> OwnerPaths);

internal sealed record ControllerClosurePaths(
    IReadOnlyList<string> EvaluatorPaths,
    IReadOnlySet<string> OwnerPaths);

internal static class ControllerClosure
{
    internal const string ProducerPath =
        "tools/StrataLint.EngineeringScope/SelfLockProbe/StrictArtifacts.cs";
    private const string EntryProject =
        "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj";
    internal static IReadOnlyList<string> RuntimePaths { get; } =
    [
        "tools/scripts/workflow/pure-revert-detect.sh",
        "tools/scripts/workflow/self-lock-probe.sh",
        "tools/scripts/report/report-supervisor.sh",
    ];

    internal static ControllerClosureSnapshot Derive(string controllerRoot)
    {
        var root = ProcessTools.RequireRepositoryRoot(controllerRoot);
        var commit = ProcessTools.GitText(root, "rev-parse", "HEAD");
        // Only the tracked path list and the handful of project files are needed. Reading the
        // whole tree here (GitRepositorySnapshotReader.ReadRevision materialises every tracked
        // blob) made each self-lock-probe invocation walk the entire repository, which pushed
        // the SelfLockProbeScriptTests process budget past its 10s hang guard in CI while
        // staying fast on a warm local checkout. The derivation below is unchanged; only the
        // way its two inputs are supplied is.
        var tracked = TrackedPathsAt(root, commit);
        var paths = DeriveCore(tracked, project => ReadTextAt(root, commit, project));
        return new ControllerClosureSnapshot(commit, paths.EvaluatorPaths, paths.OwnerPaths);
    }

    internal static ControllerClosurePaths Derive(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        var tracked = snapshot.Files.Values
            .Select(static file => file.Path.Value)
            .ToHashSet(StringComparer.Ordinal);
        return DeriveCore(tracked, project => snapshot.TryGetFile(project, out var file)
            ? file.Text
            : throw new InvalidDataException("controller project reference is absent from base"));
    }

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    private static IEnumerable<ReadOnlyMemory<byte>> SplitNul(ReadOnlyMemory<byte> bytes)
    {
        var start = 0;
        for (var index = 0; index < bytes.Length; index++)
        {
            if (bytes.Span[index] != 0) continue;
            if (index > start) yield return bytes[start..index];
            start = index + 1;
        }
        if (start < bytes.Length) yield return bytes[start..];
    }

    private static IReadOnlySet<string> TrackedPathsAt(string root, string commit)
    {
        var output = ProcessTools.Run(
            "/usr/bin/git",
            ["-C", root, "ls-tree", "-r", "--name-only", "-z", commit],
            root);
        if (output.ExitCode != 0 || output.StandardError.Length != 0)
        {
            throw new InvalidDataException("controller tree enumeration failed");
        }
        var result = new HashSet<string>(StringComparer.Ordinal);
        foreach (var bytes in SplitNul(output.StandardOutput))
        {
            var path = StrictUtf8.GetString(bytes.Span);
            EnsureCanonical(path);
            result.Add(path);
        }
        return result;
    }

    private static string ReadTextAt(string root, string commit, string path)
    {
        var output = ProcessTools.Run(
            "/usr/bin/git",
            ["-C", root, "show", $"{commit}:{path}"],
            root);
        if (output.ExitCode != 0 || output.StandardError.Length != 0)
        {
            throw new InvalidDataException("controller project reference is absent from base");
        }
        return StrictUtf8.GetString(output.StandardOutput);
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

    private static ControllerClosurePaths DeriveCore(
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

        var owners = new HashSet<string>(evaluator, StringComparer.Ordinal);
        owners.Add("tools/self-lock-probe-result.json");
        owners.Add(".github/workflows/ci.yml");
        owners.UnionWith(tracked.Where(static path => path.StartsWith(
            "tools/tests/StrataLint.ScriptTests/SelfLockProbeScriptTests.",
            StringComparison.Ordinal)));
        return new ControllerClosurePaths(
            evaluator.Order(StringComparer.Ordinal).ToArray(),
            owners);
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
