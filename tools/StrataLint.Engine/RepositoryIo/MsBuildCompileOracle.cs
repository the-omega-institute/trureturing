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
    internal static readonly TimeSpan DefaultTimeout = TimeSpan.FromSeconds(30);
    private const int MaximumOutputBytes = 32 * 1024 * 1024;
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

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
                    ["msbuild", projectPath, "-getItem:Compile", "-nologo", "-nodeReuse:false"],
                    repositoryRoot,
                    timeout ?? DefaultTimeout,
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
                             repositoryRoot,
                             projectPath))
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

    internal static SnapshotCheckout Materialize(RepositorySnapshot snapshot)
    {
        var checkout = new SnapshotCheckout();
        try
        {
            foreach (var file in snapshot.Files.Values)
            {
                var fullPath = Path.Combine(
                    checkout.Root,
                    file.Path.Value.Replace('/', Path.DirectorySeparatorChar));
                Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
                File.WriteAllBytes(fullPath, file.RawBytes.AsSpan().ToArray());
            }

            return checkout;
        }
        catch
        {
            checkout.Dispose();
            throw;
        }
    }

    private static IEnumerable<string> ParseCompilePaths(
        byte[] json,
        string repositoryRoot,
        string projectPath)
    {
        using var document = JsonDocument.Parse(StrictUtf8.GetString(json));
        if (!document.RootElement.TryGetProperty("Items", out var items)
            || !items.TryGetProperty("Compile", out var compile)
            || compile.ValueKind != JsonValueKind.Array)
        {
            throw new JsonException("MSBuild output has no Items.Compile array");
        }

        var root = Path.GetFullPath(repositoryRoot);
        foreach (var item in compile.EnumerateArray())
        {
            if (!item.TryGetProperty("FullPath", out var fullPathValue)
                || fullPathValue.GetString() is not { Length: > 0 } fullPath
                || !Path.IsPathFullyQualified(fullPath)
                || !item.TryGetProperty("Identity", out var identityValue)
                || identityValue.GetString() is not { Length: > 0 } identity)
            {
                throw new JsonException("MSBuild Compile item has no Identity and absolute FullPath");
            }

            var evaluatedPath = Path.IsPathFullyQualified(identity)
                ? identity
                : Path.Combine(root, ProjectDirectory(projectPath), identity);
            var relative = Path.GetRelativePath(root, Path.GetFullPath(evaluatedPath));
            if (relative != ".." && !relative.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal))
            {
                yield return relative.Replace(Path.DirectorySeparatorChar, '/');
            }
        }
    }

    private static string ProjectDirectory(string projectPath) =>
        projectPath.LastIndexOf('/') is var slash && slash >= 0 ? projectPath[..slash] : ".";

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
    internal SnapshotCheckout() => Root = Directory.CreateTempSubdirectory(
        "stratalint-msbuild-oracle-").FullName;

    internal string Root { get; }

    public void Dispose() => Directory.Delete(Root, recursive: true);
}
