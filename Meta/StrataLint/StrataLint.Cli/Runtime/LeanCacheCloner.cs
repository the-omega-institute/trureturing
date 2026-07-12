using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record LeanCacheCloneResult(string Strategy, string? Warning);

internal static class LeanCacheCloner
{
    internal static LeanCacheCloneResult Clone(string sourceRoot, string worktreeRoot)
    {
        var source = Path.Combine(sourceRoot, ".lake");
        var target = Path.Combine(worktreeRoot, ".lake");
        if (!Directory.Exists(source))
        {
            return new LeanCacheCloneResult(
                "skipped",
                "source has no .lake; run lake exe cache get first");
        }

        if (Directory.Exists(target)) Directory.Delete(target, recursive: true);
        var strategy = OperatingSystem.IsMacOS()
            ? TryCopy(new[] { "-c", "-R", source, target }, worktreeRoot, "apfs-clonefile")
            : OperatingSystem.IsLinux()
                ? TryCopy(new[] { "-R", "--reflink=auto", source, target }, worktreeRoot, "reflink-auto")
                : null;
        if (strategy is not null) return strategy;

        if (Directory.Exists(target)) Directory.Delete(target, recursive: true);
        var fallback = RunCopy(new[] { "-R", source, target }, worktreeRoot);
        if (fallback.ExitCode != 0)
        {
            throw new InvalidOperationException(Error(fallback, "cache copy failed"));
        }

        return new LeanCacheCloneResult(
            "copy",
            "copy-on-write cache clone failed; used slow ordinary copy");
    }

    private static LeanCacheCloneResult? TryCopy(
        string[] arguments,
        string workingDirectory,
        string strategy)
    {
        var result = RunCopy(arguments, workingDirectory);
        return result.ExitCode == 0
            ? new LeanCacheCloneResult(strategy, null)
            : null;
    }

    private static ProcessOutput RunCopy(IEnumerable<string> arguments, string workingDirectory) =>
        BoundedProcessRunner.Run(
            "cp",
            arguments,
            workingDirectory,
            TimeSpan.FromSeconds(1800),
            1024 * 1024);

    private static string Error(ProcessOutput output, string fallback)
    {
        var error = System.Text.Encoding.UTF8.GetString(output.StandardError).Trim();
        return error.Length == 0 ? fallback : error;
    }
}
