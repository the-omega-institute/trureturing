using System.Buffers;
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
        using var stream = new MemoryStream(output, writable: false);
        return ParseAsync(stream, CancellationToken.None).GetAwaiter().GetResult();
    }

    internal static async Task<IReadOnlyDictionary<string, DateTimeOffset>> ParseAsync(
        Stream stream, CancellationToken cancellation)
    {
        var parser = new HistoryParser();
        var buffer = new byte[8192];
        int count;
        while ((count = await stream.ReadAsync(buffer, cancellation).ConfigureAwait(false)) != 0)
            parser.Append(buffer.AsSpan(0, count));
        return parser.Complete();
    }

    private sealed class HistoryParser
    {
        private static readonly UTF8Encoding StrictUtf8 = new(false, true);
        private readonly ArrayBufferWriter<byte> lineBytes = new();
        private readonly Dictionary<string, DateTimeOffset> firstAdded = new(StringComparer.Ordinal);
        private DateTimeOffset? committerTime;

        internal void Append(ReadOnlySpan<byte> bytes)
        {
            while (!bytes.IsEmpty)
            {
                var newline = bytes.IndexOf((byte)'\n');
                var part = newline < 0 ? bytes : bytes[..newline];
                // Keep the existing buffer bound on each record, rather than on
                // the sum of repeated additions across the complete history.
                if (part.Length > GitRepositoryGateway.DefaultGitOutputBytes - lineBytes.WrittenCount)
                    throw new FormatException("git atom history record exceeded its buffer bound");
                lineBytes.Write(part);
                if (newline < 0) return;
                ReadLine(StrictUtf8.GetString(lineBytes.WrittenSpan));
                lineBytes.Clear();
                bytes = bytes[(newline + 1)..];
            }
        }

        internal IReadOnlyDictionary<string, DateTimeOffset> Complete()
        {
            if (lineBytes.WrittenCount != 0)
                throw new FormatException("truncated git atom history");
            return firstAdded;
        }

        private void ReadLine(string line)
        {
            if (line.Length == 0) return;
            if (line[0] == '\u001e')
            {
                if (!long.TryParse(line.AsSpan(1), NumberStyles.AllowLeadingSign,
                    CultureInfo.InvariantCulture, out var seconds))
                    throw new FormatException("invalid git committer time");
                committerTime = DateTimeOffset.FromUnixTimeSeconds(seconds);
                return;
            }

            if (committerTime is null || !DigestionCasStore.IsCanonicalPath(line))
                throw new FormatException("invalid git atom add record");
            var id = line[DigestionCasStore.RootPath.Length..];
            if (!firstAdded.TryGetValue(id, out var previous) || committerTime.Value < previous)
                firstAdded[id] = committerTime.Value;
        }
    }
}

internal sealed class GitAtomHistorySource(string repositoryRoot) : IAtomHistorySource
{
    // A process liveness guard, independent of ledger size and host throughput.
    internal static readonly TimeSpan HistoryTimeout = BoundedProcessRunner.HangDetectionBudget;

    public AtomHistory Read()
    {
        var shallow = IsShallow();
        var result = BoundedProcessRunner.RunStreaming(
            "git",
            ["log", "--full-history", "--diff-merges=separate", "--root", "--format=%x1e%ct", "--name-only",
                "--diff-filter=A", "--no-renames", "HEAD", "--", DigestionCasStore.RootPath],
            repositoryRoot,
            HistoryTimeout,
            GitRepositoryGateway.DefaultGitOutputBytes,
            AtomHistoryParser.ParseAsync);
        if (result.ExitCode != 0)
            throw new IOException($"git atom history exited {result.ExitCode}: "
                + Encoding.UTF8.GetString(result.StandardError).Trim());
        return new AtomHistory(shallow, result.StandardOutput);
    }

    private bool IsShallow()
    {
        var gitDirectory = GitWorktreeDirectory.Read(repositoryRoot)
            ?? throw new IOException("git metadata is absent");
        var commonDirectory = Path.Combine(gitDirectory, "commondir");
        if (File.Exists(commonDirectory))
            gitDirectory = Path.GetFullPath(File.ReadAllText(commonDirectory).Trim(), gitDirectory);
        return File.Exists(Path.Combine(gitDirectory, "shallow"));
    }
}

internal sealed class AtomHistoryUnavailableException(string message, Exception? inner = null)
    : InvalidOperationException(message, inner);
