using System.Collections.Immutable;
using System.ComponentModel;
using System.Text;
using System.Text.Json;

namespace StrataLint.Engine;

internal sealed record MsBuildCompileFinding(string Path, string Message);

internal sealed record MsBuildCompileMap(
    IReadOnlyDictionary<string, string> ProjectBySourcePath,
    IReadOnlyList<MsBuildCompileFinding> Findings);

internal static class MsBuildCompileOracle
{
    private const int MaximumOutputBytes = 32 * 1024 * 1024;
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static IReadOnlyDictionary<string, string> EvaluationEnvironment()
    {
        var environment = ImmutableSortedDictionary.CreateBuilder<string, string>(StringComparer.Ordinal);
        foreach (var name in new[]
                 {
                     "PATH", // The dotnet host and MSBuild tools resolve executables through PATH.
                     "HOME", // MSBuild and NuGet resolve per-user configuration under the home directory.
                     "TMPDIR", // MSBuild and NuGet use the Unix temporary-directory selector.
                     "TMP", // .NET temporary-file APIs used by MSBuild honor TMP on Windows.
                     "TEMP", // .NET temporary-file APIs used by NuGet honor TEMP on Windows.
                     "DOTNET_ROOT", // The dotnet host resolves its runtime and SDK installation here.
                     "DOTNET_HOST_PATH", // MSBuild SDK tasks use the selected dotnet host for child invocations.
                     "NUGET_PACKAGES", // NuGet resolves the global package cache from this override.
                     "LANG", // MSBuild and NuGet inherit this Unix locale for text and diagnostics.
                     "LC_ALL", // This locale override takes precedence over LANG for native host tools.
                 })
        {
            if (Environment.GetEnvironmentVariable(name) is { } value) environment.Add(name, value);
        }

        environment.Add("DOTNET_CLI_TELEMETRY_OPTOUT", "1"); // Evaluation needs no CLI telemetry.
        environment.Add("DOTNET_NOLOGO", "1"); // Keep CLI banners out of MSBuild JSON and version output.
        environment.Add("DOTNET_SKIP_FIRST_TIME_EXPERIENCE", "1"); // Evaluation must not trigger first-run setup.
        return environment.ToImmutable();
    }

    internal static MsBuildCompileMap Query(
        string repositoryRoot,
        IEnumerable<string> projectPaths,
        string? dotnetExecutable = null,
        TimeSpan? timeout = null,
        BoundedProcessRunner.ProcessRunner? run = null,
        string? configuration = null)
    {
        var owners = new Dictionary<string, string>(StringComparer.Ordinal);
        var findings = new List<MsBuildCompileFinding>();
        var dotnet = dotnetExecutable ?? ResolveDotnetExecutable();
        var environment = EvaluationEnvironment();
        foreach (var projectPath in projectPaths.Order(StringComparer.Ordinal))
        {
            try
            {
                var output = (run ?? BoundedProcessRunner.Run)(
                    dotnet,
                    QueryArguments(repositoryRoot, projectPath, configuration),
                    repositoryRoot,
                    timeout ?? BoundedProcessRunner.HangDetectionBudget,
                    MaximumOutputBytes,
                    environment: environment);
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

    private static IReadOnlyList<string> QueryArguments(string repositoryRoot, string projectPath, string? configuration)
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
        if (configuration is not null) arguments.Add($"-property:Configuration={configuration}");
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

    internal static string ResolveDotnetExecutable()
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
