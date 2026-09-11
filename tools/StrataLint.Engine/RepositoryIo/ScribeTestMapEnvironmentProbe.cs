using System.Buffers.Binary;
using System.Collections.Immutable;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;

namespace StrataLint.Engine;

internal static class ScribeTestMapEnvironmentProbe
{
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

    internal static ScribeTestMapEnvironment DescribeEnvironment() =>
        DescribeEnvironment(ResolveDotnetExecutable);

    internal static ScribeTestMapEnvironment DescribeEnvironment(
        Func<string> resolveHost,
        Func<string, ProcessOutput>? probeVersion = null,
        BoundedProcessRunner.ProcessRunner? run = null)
    {
        var environment = EvaluationEnvironment();
        var host = resolveHost();
        var output = probeVersion is not null ? probeVersion(host) : (run ?? BoundedProcessRunner.Run)(
            host, ["--version"], Directory.GetCurrentDirectory(),
            BoundedProcessRunner.HangDetectionBudget, 4096, environment: environment);
        if (output.ExitCode != 0)
        {
            throw new InvalidOperationException("dotnet-version-exit-" + output.ExitCode);
        }

        var version = StrictUtf8.GetString(output.StandardOutput).Trim();
        if (version.Length == 0)
        {
            throw new InvalidOperationException("dotnet-version-empty");
        }

        return new ScribeTestMapEnvironment(
            RuntimeInformation.RuntimeIdentifier,
            RuntimeInformation.FrameworkDescription,
            host,
            version,
            EvaluationEnvironmentDigest(environment));
    }

    private static string EvaluationEnvironmentDigest(IReadOnlyDictionary<string, string> environment)
    {
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        foreach (var (name, value) in environment.OrderBy(static entry => entry.Key, StringComparer.Ordinal))
        {
            Append(name);
            Append(value);
        }
        return Convert.ToHexStringLower(hash.GetHashAndReset());

        void Append(string value)
        {
            var bytes = StrictUtf8.GetBytes(value);
            Span<byte> length = stackalloc byte[sizeof(int)];
            BinaryPrimitives.WriteInt32BigEndian(length, bytes.Length);
            hash.AppendData(length);
            hash.AppendData(bytes);
        }
    }

    internal static bool IsBuildInput(string path)
    {
        var separator = path.LastIndexOf('/');
        var fileName = path[(separator + 1)..];
        return fileName == "global.json"
            || fileName.StartsWith("Directory.Build.", StringComparison.Ordinal)
            || fileName.StartsWith("Directory.Packages.", StringComparison.Ordinal)
            || fileName.Equals("NuGet.Config", StringComparison.OrdinalIgnoreCase)
            || fileName.EndsWith(".props", StringComparison.Ordinal)
            || fileName.EndsWith(".targets", StringComparison.Ordinal);
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
