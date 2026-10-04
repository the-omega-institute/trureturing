using System.Collections.Immutable;
using System.ComponentModel;
using System.Diagnostics;
using System.Text.Json;

namespace StrataLint.Scribe;

public sealed record ScribeSdkDiagnostic(string DefinitionPath, string Id, string Location, string Message)
{
    public override string ToString() => $"ScribeSdkDiagnostic: {DefinitionPath}: {Location}: {Id}: {Message}";
}

public sealed record ScribeSdkAdmissionResult(
    int ExitCode, ImmutableArray<string> Paths, ImmutableArray<ScribeSdkDiagnostic> Diagnostics,
    string? InfrastructureFailure)
{
    public void WriteFailure(TextWriter error)
    {
        foreach (var diagnostic in Diagnostics) error.WriteLine(diagnostic);
        if (InfrastructureFailure is not null) error.WriteLine("ScribeSdkInfrastructure: " + InfrastructureFailure);
    }
}

public sealed class ScribeSdkAdmissionException(int exitCode, string message) : InvalidOperationException(message)
{
    public int ExitCode { get; } = exitCode;
}

/// <summary>SDK diagnostics for daily selections; this component never executes a definition.</summary>
public static class ScribeSdkAdmission
{
    /// <summary>
    /// The SDK host is an explicit argument, SCRIBE_DOTNET, DOTNET_HOST_PATH, or DOTNET_ROOT.
    /// Empty selections do not need an SDK. Configuration changes expand diagnostics only.
    /// </summary>
    public static ScribeSdkAdmissionResult Check(string repositoryRoot, IEnumerable<string> executionPaths,
        IEnumerable<string> changedPaths, string? dotnetPath = null)
    {
        var paths = SelectPaths(repositoryRoot, executionPaths, changedPaths);
        if (paths.IsEmpty) return new(0, paths, [], null);
        try
        {
            var host = dotnetPath ?? ResolveDotnet();
            if (string.IsNullOrWhiteSpace(host) || !Path.IsPathFullyQualified(host) || !File.Exists(host))
                return new(2, paths, [], "a readable absolute SDK host path is required (SCRIBE_DOTNET or DOTNET_ROOT)");
            using var batch = ScribeSdkBatch.Create(repositoryRoot, paths);
            var start = new ProcessStartInfo(host)
            {
                WorkingDirectory = Path.GetFullPath(repositoryRoot),
                UseShellExecute = false,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
            };
            foreach (var argument in new[] { "msbuild", batch.ProjectPath, "-target:Build", "-maxcpucount",
                "-nodeReuse:false", "-verbosity:quiet", "-nologo" })
                start.ArgumentList.Add(argument);
            using var process = Process.Start(start)
                ?? throw new InvalidOperationException("could not start the SDK host");
            var stdout = process.StandardOutput.ReadToEndAsync();
            var stderr = process.StandardError.ReadToEndAsync();
            process.WaitForExit();
            var log = stdout.GetAwaiter().GetResult() + stderr.GetAwaiter().GetResult();
            var diagnostics = batch.ReadDiagnostics();
            if (process.ExitCode != 0 && diagnostics.IsEmpty)
                return new(2, paths, [], $"SDK invocation exited {process.ExitCode}: {log.Trim()}");
            return new(diagnostics.IsEmpty ? 0 : 1, paths, diagnostics, null);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or InvalidOperationException or ArgumentException or Win32Exception or JsonException)
        {
            return new(2, paths, [], exception.Message);
        }
    }

    internal static ImmutableArray<string> SelectPaths(string root, IEnumerable<string> executionPaths,
        IEnumerable<string> changedPaths) =>
        (changedPaths.Any(IsConfigurationPath)
            ? Directory.EnumerateFiles(Path.Combine(root, "Blueprint"), "*.scribe.cs", SearchOption.AllDirectories)
                .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/'))
            : executionPaths).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray();

    private static bool IsConfigurationPath(string path)
    {
        var normalized = path.Replace('\\', '/');
        if (normalized.StartsWith("./", StringComparison.Ordinal)) normalized = normalized[2..];
        return normalized is ".editorconfig" or "Directory.Build.props" or "Directory.Build.targets"
            or "Directory.Packages.props" or "global.json"
            || normalized.StartsWith("tools/Architecture/BannedSymbols", StringComparison.Ordinal)
                && normalized.EndsWith(".txt", StringComparison.Ordinal);
    }

    private static string? ResolveDotnet()
    {
        var explicitHost = Environment.GetEnvironmentVariable("SCRIBE_DOTNET")
            ?? Environment.GetEnvironmentVariable("DOTNET_HOST_PATH");
        if (explicitHost is not null) return explicitHost;
        var root = Environment.GetEnvironmentVariable("DOTNET_ROOT");
        return string.IsNullOrWhiteSpace(root) ? null : Path.Combine(root, OperatingSystem.IsWindows() ? "dotnet.exe" : "dotnet");
    }
}
