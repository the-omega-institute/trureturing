using System.Globalization;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal interface IAtomHistorySource
{
    AtomHistory Read();
}

internal sealed record AtomHistory(
    bool IsShallow,
    IReadOnlyDictionary<string, DateTimeOffset> FirstAdded);

internal static class AtomHistoryParser
{
    internal static IReadOnlyDictionary<string, DateTimeOffset> Parse(byte[] output)
    {
        var text = new UTF8Encoding(false, true).GetString(output);
        if (text.Length > 0 && !text.EndsWith('\n'))
            throw new FormatException("truncated git atom history");

        var firstAdded = new Dictionary<string, DateTimeOffset>(StringComparer.Ordinal);
        DateTimeOffset? committerTime = null;
        foreach (var line in text.Split('\n'))
        {
            if (line.Length == 0) continue;
            if (line[0] == '\u001e')
            {
                if (!long.TryParse(line.AsSpan(1), NumberStyles.AllowLeadingSign,
                    CultureInfo.InvariantCulture, out var seconds))
                    throw new FormatException("invalid git committer time");
                committerTime = DateTimeOffset.FromUnixTimeSeconds(seconds);
                continue;
            }

            if (committerTime is null || !DigestionCasStore.IsCanonicalPath(line))
                throw new FormatException("invalid git atom add record");
            var id = line[DigestionCasStore.RootPath.Length..];
            if (!firstAdded.TryGetValue(id, out var previous) || committerTime.Value < previous)
                firstAdded[id] = committerTime.Value;
        }

        return firstAdded;
    }
}

internal sealed class GitAtomHistorySource(string repositoryRoot) : IAtomHistorySource
{
    // A process liveness guard, independent of ledger size and host throughput.
    internal static readonly TimeSpan HistoryTimeout = BoundedProcessRunner.HangDetectionBudget;

    public AtomHistory Read()
    {
        var shallow = IsShallow();
        var result = new ProductionGitProcessRunner().Run(
            "git",
            ["log", "--full-history", "-m", "--format=%x1e%ct", "--name-only",
                "--diff-filter=A", "--no-renames", "HEAD", "--", DigestionCasStore.RootPath],
            repositoryRoot,
            HistoryTimeout,
            GitRepositoryGateway.DefaultGitOutputBytes);
        if (result.ExitCode != 0)
            throw new IOException($"git atom history exited {result.ExitCode}: "
                + Encoding.UTF8.GetString(result.StandardError).Trim());
        return new AtomHistory(shallow, AtomHistoryParser.Parse(result.StandardOutput));
    }

    private bool IsShallow()
    {
        var gitDirectory = Path.Combine(repositoryRoot, ".git");
        if (File.Exists(gitDirectory))
        {
            var pointer = File.ReadAllText(gitDirectory).Trim();
            const string prefix = "gitdir: ";
            if (!pointer.StartsWith(prefix, StringComparison.Ordinal))
                throw new IOException("invalid git directory pointer");
            gitDirectory = Path.GetFullPath(pointer[prefix.Length..], repositoryRoot);
        }

        if (!Directory.Exists(gitDirectory)) throw new IOException("git metadata is absent");
        var commonDirectory = Path.Combine(gitDirectory, "commondir");
        if (File.Exists(commonDirectory))
            gitDirectory = Path.GetFullPath(File.ReadAllText(commonDirectory).Trim(), gitDirectory);
        return File.Exists(Path.Combine(gitDirectory, "shallow"));
    }
}

internal sealed class AtomHistoryUnavailableException(string message, Exception? inner = null)
    : InvalidOperationException(message, inner);
