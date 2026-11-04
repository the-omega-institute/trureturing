using System.Buffers;
using System.Text;
using StrataLint.Runtime;

namespace StrataLint.Engine;

internal static class GitRepositoryTreeStream
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static GitRepositoryTreeEntry[] Read(string revision,
        GitStreamReader<GitRepositoryTreeEntry[]> runGit)
    {
        ArgumentNullException.ThrowIfNull(runGit);
        // Bound diagnostics independently of the complete repository inventory.
        var result = runGit(["ls-tree", "-r", "-l", "-z", revision], 64 * 1024 * 1024,
            default, Parse);
        if (result.ExitCode != 0)
            throw new InvalidOperationException(StrictUtf8.GetString(result.StandardError).Trim() is { Length: > 0 } error
                ? error : "git command failed");
        return result.StandardOutput;
    }

    internal static async Task<GitRepositoryTreeEntry[]> Parse(Stream output, CancellationToken cancellation)
    {
        var entries = new List<GitRepositoryTreeEntry>();
        var record = new ArrayBufferWriter<byte>();
        var buffer = new byte[64 * 1024];
        int count;
        while ((count = await output.ReadAsync(buffer, cancellation).ConfigureAwait(false)) != 0)
        {
            var start = 0;
            for (var index = 0; index < count; index++)
            {
                if (buffer[index] != 0) continue;
                record.Write(buffer.AsSpan(start, index - start));
                entries.Add(ParseEntry(record.WrittenSpan));
                record.Clear();
                start = index + 1;
            }
            record.Write(buffer.AsSpan(start, count - start));
        }
        if (record.WrittenCount != 0)
            throw new InvalidOperationException("git tree emitted an unterminated entry");
        return entries.ToArray();
    }

    private static GitRepositoryTreeEntry ParseEntry(ReadOnlySpan<byte> entry)
    {
        var tab = entry.IndexOf((byte)'\t');
        if (tab <= 0) throw new InvalidOperationException("git tree emitted invalid metadata");
        var metadata = StrictUtf8.GetString(entry[..tab]).Split(' ', StringSplitOptions.RemoveEmptyEntries);
        var path = StrictUtf8.GetString(entry[(tab + 1)..]);
        if (metadata.Length is not (3 or 4) || !RepoPath.TryCreate(path, out _))
            throw new InvalidOperationException($"git tree emitted invalid entry: {path}");
        long? size = null;
        if (metadata.Length == 4 && metadata[3] != "-")
        {
            if (!long.TryParse(metadata[3], System.Globalization.NumberStyles.None,
                    System.Globalization.CultureInfo.InvariantCulture, out var parsedSize))
                throw new InvalidOperationException($"git tree emitted invalid entry: {path}");
            size = parsedSize;
        }
        return new GitRepositoryTreeEntry(metadata[0], metadata[1], metadata[2], path, size);
    }
}
