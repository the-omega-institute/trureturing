using System.Diagnostics;
using System.Text;

namespace StrataLint.EngineeringScope;

internal sealed record CommandOutput(int ExitCode, byte[] StandardOutput, byte[] StandardError);

internal static class ProcessTools
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static CommandOutput Run(
        string executable,
        IReadOnlyList<string> arguments,
        string workingDirectory)
    {
        var startInfo = new ProcessStartInfo
        {
            FileName = executable,
            WorkingDirectory = workingDirectory,
            UseShellExecute = false,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
        };
        foreach (var argument in arguments)
        {
            startInfo.ArgumentList.Add(argument);
        }

        using var process = Process.Start(startInfo)
            ?? throw new InvalidOperationException($"failed to start {executable}");
        using var standardOutput = new MemoryStream();
        using var standardError = new MemoryStream();
        var outputCopy = process.StandardOutput.BaseStream.CopyToAsync(standardOutput);
        var errorCopy = process.StandardError.BaseStream.CopyToAsync(standardError);
        process.WaitForExit();
        Task.WhenAll(outputCopy, errorCopy).GetAwaiter().GetResult();
        return new CommandOutput(
            process.ExitCode,
            standardOutput.ToArray(),
            standardError.ToArray());
    }

    internal static string GitText(string repository, params string[] arguments)
    {
        var output = Run("/usr/bin/git", ["-C", repository, .. arguments], repository);
        if (output.ExitCode != 0 || output.StandardError.Length != 0)
        {
            throw new InvalidDataException("git query failed");
        }
        try
        {
            return StrictUtf8.GetString(output.StandardOutput).TrimEnd('\n', '\r');
        }
        catch (DecoderFallbackException exception)
        {
            throw new InvalidDataException("git output is not strict UTF-8", exception);
        }
    }

    internal static string RequireRepositoryRoot(string repository)
    {
        var requested = Path.GetFullPath(repository);
        if (!Directory.Exists(requested))
        {
            throw new DirectoryNotFoundException("repository is absent");
        }
        var physical = PhysicalDirectory(requested);
        var root = GitText(physical, "rev-parse", "--show-toplevel");
        if (!string.Equals(
                Path.TrimEndingDirectorySeparator(physical),
                Path.TrimEndingDirectorySeparator(PhysicalDirectory(root)),
                StringComparison.Ordinal))
        {
            throw new InvalidDataException("repository argument must name its physical root");
        }
        return physical;
    }

    private static string PhysicalDirectory(string directory)
    {
        var output = Run("/bin/pwd", ["-P"], directory);
        if (output.ExitCode != 0 || output.StandardError.Length != 0)
        {
            throw new InvalidDataException("physical directory resolution failed");
        }
        try
        {
            return StrictUtf8.GetString(output.StandardOutput).TrimEnd('\n', '\r');
        }
        catch (DecoderFallbackException exception)
        {
            throw new InvalidDataException("physical path is not strict UTF-8", exception);
        }
    }
}
