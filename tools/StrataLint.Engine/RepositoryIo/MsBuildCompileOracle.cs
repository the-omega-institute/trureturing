using System.ComponentModel;
using System.Text;
using System.Text.Json;
using System.Xml.Linq;

namespace StrataLint.Engine;

internal sealed record MsBuildCompileFinding(string Path, string Message);

internal sealed record MsBuildCompileMap(
    IReadOnlyDictionary<string, string> ProjectBySourcePath,
    IReadOnlyList<MsBuildCompileFinding> Findings);

internal static class MsBuildCompileOracle
{
    private const int MaximumOutputBytes = 32 * 1024 * 1024;
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static bool IsBuildInput(string path)
    {
        var separator = path.LastIndexOf('/');
        var fileName = path[(separator + 1)..];
        return fileName == "global.json"
            || IsDirectoryBuildChainFileName(fileName)
            || fileName.Equals("NuGet.Config", StringComparison.OrdinalIgnoreCase)
            || IsPropsOrTargetsFileName(fileName);
    }

    internal static EffectiveDerivationInputProjection CreateEffectiveDerivationInputProjection(
        RepositorySnapshot snapshot,
        Func<string, bool> isSeed,
        IReadOnlyList<string> projectPaths)
    {
        var included = snapshot.Files.Values
            .Where(file => isSeed(file.Path.Value))
            .ToDictionary(static file => file.Path.Value, StringComparer.Ordinal);
        var pending = new Queue<string>(projectPaths
            .Concat(included.Keys.Where(IsPropsOrTargetsInput))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal));
        foreach (var file in snapshot.Files.Values.Where(file =>
                     IsDirectoryBuildChainInput(file.Path.Value)
                     && projectPaths.Any(project => IsAncestorDirectory(
                         DirectoryOf(file.Path.Value),
                         DirectoryOf(project)))))
        {
            included[file.Path.Value] = file;
            pending.Enqueue(file.Path.Value);
        }

        var scanned = new HashSet<string>(StringComparer.Ordinal);
        var existsReferences = new HashSet<string>(StringComparer.Ordinal);
        while (pending.TryDequeue(out var path))
        {
            if (!scanned.Add(path) || !snapshot.TryGetFile(path, out var file))
            {
                continue;
            }

            XDocument document;
            try
            {
                document = XDocument.Parse(file.Text, LoadOptions.None);
            }
            catch (Exception exception) when (exception is InvalidOperationException or System.Xml.XmlException)
            {
                return EffectiveDerivationInputProjection.Full(snapshot);
            }

            if (document.Root?.Name.LocalName != "Project"
                || HasUnclosedDirectoryEnumeration(document))
            {
                return EffectiveDerivationInputProjection.Full(snapshot);
            }

            foreach (var condition in document.Descendants()
                         .Attributes()
                         .Where(static attribute => attribute.Name.LocalName == "Condition")
                         .Select(static attribute => attribute.Value))
            {
                if (!TryCollectExistsReferences(path, condition, existsReferences))
                {
                    return EffectiveDerivationInputProjection.Full(snapshot);
                }
            }

            foreach (var import in document.Descendants()
                         .Where(static element => element.Name.LocalName == "Import"))
            {
                var importValue = (string?)import.Attribute("Project");
                if (string.IsNullOrWhiteSpace(importValue)
                    || !TryResolveImport(snapshot, path, importValue, out var importedPath))
                {
                    return EffectiveDerivationInputProjection.Full(snapshot);
                }

                if (importedPath is null
                    || !snapshot.TryGetFile(importedPath, out var importedFile))
                {
                    continue;
                }

                included[importedPath] = importedFile;
                pending.Enqueue(importedPath);
            }
        }

        if (existsReferences.Any(path =>
                snapshot.TryGetFile(path, out _) && !included.ContainsKey(path)))
        {
            return EffectiveDerivationInputProjection.Full(snapshot);
        }

        return EffectiveDerivationInputProjection.Sparse(snapshot, included.Values);
    }

    internal static MsBuildCompileMap Query(
        string repositoryRoot,
        IEnumerable<string> projectPaths,
        string? dotnetExecutable = null,
        TimeSpan? timeout = null)
    {
        var owners = new Dictionary<string, string>(StringComparer.Ordinal);
        var findings = new List<MsBuildCompileFinding>();
        var dotnet = dotnetExecutable ?? ResolveDotnetExecutable();
        foreach (var projectPath in projectPaths.Order(StringComparer.Ordinal))
        {
            try
            {
                var output = BoundedProcessRunner.Run(
                    dotnet,
                    QueryArguments(repositoryRoot, projectPath),
                    repositoryRoot,
                    timeout ?? BoundedProcessRunner.HangDetectionBudget,
                    MaximumOutputBytes);
                if (output.ExitCode != 0)
                {
                    throw new InvalidOperationException(
                        StrictUtf8.GetString(output.StandardError).Trim() is { Length: > 0 } error
                            ? error
                            : $"dotnet msbuild exited {output.ExitCode}");
                }

                foreach (var sourcePath in ParseCompilePaths(
                             output.StandardOutput,
                             repositoryRoot))
                {
                    if (owners.TryGetValue(sourcePath, out var owner) && owner != projectPath)
                    {
                        findings.Add(new MsBuildCompileFinding(
                            sourcePath,
                            $"MSBuild Compile ownership is ambiguous between {owner} and {projectPath}"));
                        continue;
                    }

                    owners[sourcePath] = projectPath;
                }
            }
            catch (Exception exception) when (exception is InvalidOperationException
                or JsonException
                or DecoderFallbackException
                or IOException
                or UnauthorizedAccessException
                or TimeoutException
                or Win32Exception)
            {
                findings.Add(new MsBuildCompileFinding(
                    projectPath,
                    $"MSBuild Compile query failed closed: {exception.Message}"));
            }
        }

        return new MsBuildCompileMap(owners, findings);
    }

    internal static SnapshotCheckout Materialize(EffectiveDerivationInputProjection projection)
    {
        var checkout = new SnapshotCheckout();
        try
        {
            foreach (var file in projection.Files)
            {
                checkout.Write(file);
            }

            return checkout;
        }
        catch
        {
            checkout.Dispose();
            throw;
        }
    }

    private static bool IsDirectoryBuildChainFileName(string fileName) =>
        fileName.StartsWith("Directory.Build.", StringComparison.Ordinal)
        || fileName.StartsWith("Directory.Packages.", StringComparison.Ordinal);

    private static bool IsPropsOrTargetsFileName(string fileName) =>
        fileName.EndsWith(".props", StringComparison.Ordinal)
        || fileName.EndsWith(".targets", StringComparison.Ordinal);

    private static bool IsPropsOrTargetsInput(string path)
    {
        var separator = path.LastIndexOf('/');
        return IsPropsOrTargetsFileName(path[(separator + 1)..]);
    }

    private static bool IsDirectoryBuildChainInput(string path)
    {
        var separator = path.LastIndexOf('/');
        return IsDirectoryBuildChainFileName(path[(separator + 1)..]);
    }

    private static bool IsAncestorDirectory(string ancestor, string directory) =>
        ancestor.Length == 0
        || directory == ancestor
        || directory.StartsWith(ancestor + "/", StringComparison.Ordinal);

    private static string DirectoryOf(string path) =>
        path.LastIndexOf('/') is var separator && separator >= 0 ? path[..separator] : string.Empty;

    private static bool HasUnclosedDirectoryEnumeration(XDocument document)
    {
        foreach (var element in document.Descendants())
        {
            foreach (var attribute in element.Attributes())
            {
                var value = attribute.Value;
                if (value.Contains("$([System.IO.Directory]::", StringComparison.OrdinalIgnoreCase)
                    || value.Contains("GetFiles(", StringComparison.OrdinalIgnoreCase)
                    || value.Contains("GetDirectories(", StringComparison.OrdinalIgnoreCase))
                {
                    return true;
                }

                if ((value.Contains('*') || value.Contains('?'))
                    && !(element.Name.LocalName == "Compile"
                        && value.EndsWith(".cs", StringComparison.Ordinal)))
                {
                    return true;
                }
            }
        }

        return false;
    }

    private static bool TryCollectExistsReferences(
        string importingPath,
        string condition,
        ISet<string> references)
    {
        var offset = 0;
        while ((offset = condition.IndexOf("Exists", offset, StringComparison.OrdinalIgnoreCase)) >= 0)
        {
            var cursor = offset + "Exists".Length;
            SkipWhitespace(condition, ref cursor);
            if (cursor >= condition.Length || condition[cursor++] != '(')
            {
                return false;
            }
            SkipWhitespace(condition, ref cursor);
            if (cursor >= condition.Length || condition[cursor] is not ('\'' or '"'))
            {
                return false;
            }

            var quote = condition[cursor++];
            var end = condition.IndexOf(quote, cursor);
            if (end < 0)
            {
                return false;
            }

            var value = condition[cursor..end];
            cursor = end + 1;
            SkipWhitespace(condition, ref cursor);
            if (cursor >= condition.Length || condition[cursor++] != ')'
                || !IsLiteralPath(value))
            {
                return false;
            }

            var resolved = ResolveRepositoryRelativePath(importingPath, value);
            if (resolved is not null)
            {
                references.Add(resolved);
            }
            offset = cursor;
        }

        return true;
    }

    private static void SkipWhitespace(string value, ref int cursor)
    {
        while (cursor < value.Length && char.IsWhiteSpace(value[cursor]))
        {
            cursor++;
        }
    }

    private static bool TryResolveImport(
        RepositorySnapshot snapshot,
        string importingPath,
        string value,
        out string? importedPath)
    {
        if (IsLiteralPath(value))
        {
            importedPath = ResolveRepositoryRelativePath(importingPath, value);
            return true;
        }

        return TryResolveDirectoryBuildFileAbove(snapshot, importingPath, value, out importedPath);
    }

    private static bool IsLiteralPath(string value) =>
        !string.IsNullOrWhiteSpace(value)
        && !value.Contains("$(", StringComparison.Ordinal)
        && !value.Contains("@(", StringComparison.Ordinal)
        && !value.Contains("%(", StringComparison.Ordinal)
        && !value.Contains('*')
        && !value.Contains('?')
        && !value.Contains(';');

    private static bool TryResolveDirectoryBuildFileAbove(
        RepositorySnapshot snapshot,
        string importingPath,
        string value,
        out string? importedPath)
    {
        const string Prefix = "$([MSBuild]::GetPathOfFileAbove('";
        const string Suffix = "', '$(MSBuildThisFileDirectory)..'))";
        importedPath = null;
        if (!value.StartsWith(Prefix, StringComparison.Ordinal)
            || !value.EndsWith(Suffix, StringComparison.Ordinal))
        {
            return false;
        }

        var fileName = value[Prefix.Length..^Suffix.Length];
        if (!IsDirectoryBuildChainFileName(fileName)
            || fileName.Contains('/')
            || fileName.Contains('\\'))
        {
            return false;
        }

        var directory = DirectoryOf(DirectoryOf(importingPath));
        while (true)
        {
            var candidate = directory.Length == 0 ? fileName : directory + "/" + fileName;
            if (snapshot.TryGetFile(candidate, out _))
            {
                importedPath = candidate;
                return true;
            }
            if (directory.Length == 0)
            {
                return true;
            }
            directory = DirectoryOf(directory);
        }
    }

    private static string? ResolveRepositoryRelativePath(string importingPath, string value)
    {
        var normalized = value.Replace('\\', '/');
        if (Path.IsPathFullyQualified(normalized))
        {
            return null;
        }

        var segments = new List<string>();
        var directory = DirectoryOf(importingPath);
        if (directory.Length != 0)
        {
            segments.AddRange(directory.Split('/'));
        }
        foreach (var segment in normalized.Split('/', StringSplitOptions.RemoveEmptyEntries))
        {
            if (segment == ".")
            {
                continue;
            }
            if (segment == "..")
            {
                if (segments.Count == 0)
                {
                    return null;
                }
                segments.RemoveAt(segments.Count - 1);
                continue;
            }
            segments.Add(segment);
        }

        return string.Join('/', segments);
    }

    private static IEnumerable<string> ParseCompilePaths(
        byte[] json,
        string repositoryRoot)
    {
        using var document = JsonDocument.Parse(StrictUtf8.GetString(json));
        if (!document.RootElement.TryGetProperty("Items", out var items)
            || !items.TryGetProperty("Compile", out var compile)
            || compile.ValueKind != JsonValueKind.Array)
        {
            throw new JsonException("MSBuild output has no Items.Compile array");
        }

        var root = CanonicalizePath(repositoryRoot);
        foreach (var item in compile.EnumerateArray())
        {
            if (!item.TryGetProperty("FullPath", out var fullPathValue)
                || fullPathValue.GetString() is not { Length: > 0 } fullPath
                || !Path.IsPathFullyQualified(fullPath)
                || ContainsParentTraversal(fullPath))
            {
                throw new JsonException("MSBuild Compile item has no traversal-free absolute FullPath");
            }

            var relative = Path.GetRelativePath(root, CanonicalizePath(fullPath));
            if (relative != ".." && !relative.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal))
            {
                yield return relative.Replace(Path.DirectorySeparatorChar, '/');
            }
        }
    }

    private static IReadOnlyList<string> QueryArguments(string repositoryRoot, string projectPath)
    {
        var props = FindDirectoryBuildFile(repositoryRoot, projectPath, "Directory.Build.props");
        var targets = FindDirectoryBuildFile(repositoryRoot, projectPath, "Directory.Build.targets");
        var arguments = new List<string>
        {
            "msbuild",
            projectPath,
            "-getItem:Compile",
            "-nologo",
            "-noAutoResponse",
            "-nodeReuse:false",
            $"-property:ImportDirectoryBuildProps={(props is null ? "false" : "true")}",
            $"-property:ImportDirectoryBuildTargets={(targets is null ? "false" : "true")}",
        };
        if (props is not null) arguments.Add($"-property:DirectoryBuildPropsPath={props}");
        if (targets is not null) arguments.Add($"-property:DirectoryBuildTargetsPath={targets}");
        return arguments;
    }

    private static string? FindDirectoryBuildFile(
        string repositoryRoot,
        string projectPath,
        string fileName)
    {
        var root = Path.TrimEndingDirectorySeparator(Path.GetFullPath(repositoryRoot));
        var current = Directory.GetParent(Path.GetFullPath(projectPath, root));
        while (current is not null)
        {
            var relative = Path.GetRelativePath(root, current.FullName);
            if (relative == ".." || relative.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal))
            {
                break;
            }

            var candidate = Path.Combine(current.FullName, fileName);
            if (File.Exists(candidate)) return candidate;
            if (relative == ".") break;
            current = current.Parent;
        }

        return null;
    }

    private static bool ContainsParentTraversal(string path) => path
        .Split(['/', '\\'], StringSplitOptions.RemoveEmptyEntries)
        .Contains("..", StringComparer.Ordinal);

    private static string CanonicalizePath(string path)
    {
        var fullPath = Path.GetFullPath(path);
        var root = Path.GetPathRoot(fullPath)!;
        var current = root;
        foreach (var segment in fullPath[root.Length..]
                     .Split(Path.DirectorySeparatorChar, StringSplitOptions.RemoveEmptyEntries))
        {
            var candidate = Path.Combine(current, segment);
            FileSystemInfo info = Directory.Exists(candidate)
                ? new DirectoryInfo(candidate)
                : new FileInfo(candidate);
            if (info.ResolveLinkTarget(returnFinalTarget: true) is { } target)
            {
                candidate = target.FullName;
            }

            current = candidate;
        }

        return Path.TrimEndingDirectorySeparator(current);
    }

    private static string ResolveDotnetExecutable()
    {
        if (Environment.GetEnvironmentVariable("DOTNET_HOST_PATH") is { Length: > 0 } host
            && File.Exists(host))
        {
            return host;
        }

        if (Environment.GetEnvironmentVariable("DOTNET_ROOT") is { Length: > 0 } root
            && File.Exists(Path.Combine(root, "dotnet")))
        {
            return Path.Combine(root, "dotnet");
        }

        var userInstall = Path.Combine(
            Environment.GetFolderPath(Environment.SpecialFolder.UserProfile),
            ".dotnet",
            "dotnet");
        return File.Exists(userInstall) ? userInstall : "dotnet";
    }
}

internal sealed class SnapshotCheckout : IDisposable
{
    private readonly List<string> materializedPaths = [];

    internal SnapshotCheckout() => Root = Directory.CreateTempSubdirectory(
        "stratalint-msbuild-oracle-").FullName;

    internal string Root { get; }

    internal IReadOnlyList<string> MaterializedPaths => materializedPaths;

    internal void Write(RepositoryFile file)
    {
        var fullPath = Path.Combine(
            Root,
            file.Path.Value.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
        File.WriteAllBytes(fullPath, file.RawBytes.AsSpan().ToArray());
        materializedPaths.Add(file.Path.Value);
    }

    public void Dispose() => Directory.Delete(Root, recursive: true);
}
