using System.Diagnostics;
using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

internal sealed record CapacityFinding(string Path, string Message);

// SL-003 capacity durable net: a dotnet-test-visible mirror of the admission
// Capacity rule (RepositoryRules.Capacity). The admission rule runs only under
// `make gate` / `make preflight`; this policy re-checks the same invariant during
// `dotnet test` so an oversize artifact or an over-full directory is caught
// locally before it reaches the CI baseline admission (SL-003 has repeatedly
// slipped past `dotnet test`). Thresholds, exclusions, and the line-count formula
// are reused from the engine's single source (RepositoryRules), so the two nets
// never drift.
internal static class CapacityPolicy
{
    internal static IReadOnlyList<CapacityFinding> InspectRepository(string repositoryRoot)
    {
        var files = new List<(string Path, string Text)>();
        foreach (var relativePath in TrackedPaths(repositoryRoot))
        {
            var fullPath = Path.Combine(repositoryRoot, relativePath);
            if (!File.Exists(fullPath))
            {
                continue;
            }

            files.Add((relativePath, File.ReadAllText(fullPath)));
        }

        return InspectFiles(files);
    }

    // Pure core shared by InspectRepository and the RED fixtures: applies the
    // engine's capacity exclusions, hard line limit, and directory file limit.
    internal static IReadOnlyList<CapacityFinding> InspectFiles(
        IEnumerable<(string Path, string Text)> files)
    {
        var findings = new List<CapacityFinding>();
        var directories = new Dictionary<string, int>(StringComparer.Ordinal);
        foreach (var (path, text) in files)
        {
            if (RepositoryRules.IsCapacityExcluded(path))
            {
                continue;
            }

            var lineCount = RepositoryRules.CountArtifactLines(text);
            if (lineCount > RepositoryRules.ArtifactHardLineLimit)
            {
                findings.Add(new CapacityFinding(
                    path,
                    $"artifact spans {lineCount} lines (hard limit {RepositoryRules.ArtifactHardLineLimit})"));
            }

            var slash = path.LastIndexOf('/');
            var directory = slash < 0 ? "." : path[..slash];
            directories[directory] = directories.GetValueOrDefault(directory) + 1;
        }

        findings.AddRange(directories
            .Where(item => item.Value > RepositoryRules.DirectoryFileLimit)
            .OrderBy(static item => item.Key, StringComparer.Ordinal)
            .Select(static item => new CapacityFinding(
                item.Key,
                $"directory contains {item.Value} files (maximum {RepositoryRules.DirectoryFileLimit})")));
        return findings;
    }

    private static IReadOnlyList<string> TrackedPaths(string repositoryRoot)
    {
        var startInfo = new ProcessStartInfo("git")
        {
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        startInfo.ArgumentList.Add("-C");
        startInfo.ArgumentList.Add(repositoryRoot);
        startInfo.ArgumentList.Add("ls-files");
        startInfo.ArgumentList.Add("-z");
        using var process = Process.Start(startInfo)
            ?? throw new InvalidOperationException("could not start git ls-files for capacity policy");
        var output = process.StandardOutput.ReadToEnd();
        var error = process.StandardError.ReadToEnd();
        process.WaitForExit();
        if (process.ExitCode != 0)
        {
            throw new InvalidOperationException(
                $"git ls-files failed with exit {process.ExitCode}: {error}");
        }

        return output.Split('\0', StringSplitOptions.RemoveEmptyEntries);
    }
}
