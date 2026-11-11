using StrataLint.Runtime;
using System.Buffers;
using System.Text;

namespace StrataLint.Engine;

internal static class GitIndexRepositoryFiles
{
    private const int MaximumDiagnosticBytes = 64 * 1024 * 1024;
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static IReadOnlyList<(string RelativePath, string FullPath)> Enumerate(
        string repositoryRoot) => EnumerateTracked(repositoryRoot)
        .Select(entry => (
            RelativePath: entry.RelativePath,
            FullPath: Path.Combine(
                repositoryRoot,
                entry.RelativePath.Replace('/', Path.DirectorySeparatorChar))))
        .Where(static file => File.Exists(file.FullPath))
        .ToArray();

    internal static IReadOnlyList<(string RelativePath, string Mode)> EnumerateTracked(
        string repositoryRoot) => Read(repositoryRoot)
        .OrderBy(static pair => pair.Key, StringComparer.Ordinal)
        .Select(static pair => (RelativePath: pair.Key, Mode: pair.Value.Mode))
        .ToArray();

    internal static Dictionary<string, GitIndexEntry> Read(string repositoryRoot,
        IReadOnlyList<string>? pathspecs = null) => Read(pathspecs ?? [],
        (arguments, maximumErrorBytes, input, readOutput) => BoundedProcessRunner.RunStreaming(
            "git", arguments, repositoryRoot, TimeSpan.FromSeconds(120), maximumErrorBytes,
            readOutput, input));

    internal static Dictionary<string, GitIndexEntry> Read(IReadOnlyList<string> pathspecs,
        GitStreamReader<Dictionary<string, GitIndexEntry>> runGit)
    {
        // Stream the complete inventory; only stderr retains the process output bound.
        var result = runGit(["ls-files", "--stage", "-z", .. pathspecs],
            MaximumDiagnosticBytes, default, Parse);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException(
                StrictUtf8.GetString(result.StandardError).Trim() is { Length: > 0 } error
                    ? error
                    : "git ls-files --stage failed");
        }

        return result.StandardOutput;
    }

    internal static async Task<Dictionary<string, GitIndexEntry>> Parse(Stream output,
        CancellationToken cancellation)
    {
        var paths = new Dictionary<string, GitIndexEntry>(StringComparer.Ordinal);
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
                AddEntry(paths, record.WrittenSpan);
                record.Clear();
                start = index + 1;
            }
            record.Write(buffer.AsSpan(start, count - start));
        }
        if (record.WrittenCount != 0)
            throw new InvalidOperationException("git index emitted an unterminated entry");
        return paths;
    }

    private static void AddEntry(Dictionary<string, GitIndexEntry> paths, ReadOnlySpan<byte> entry)
    {
        var tab = entry.IndexOf((byte)'\t');
        if (tab <= 0)
            throw new InvalidOperationException("git index emitted invalid metadata");
        var metadata = StrictUtf8.GetString(entry[..tab]).Split(' ');
        var path = StrictUtf8.GetString(entry[(tab + 1)..]);
        if (metadata.Length != 3 || metadata[2] != "0"
            || !paths.TryAdd(path, new GitIndexEntry(metadata[0], metadata[1])))
            throw new InvalidOperationException($"unmerged or duplicate repository entry: {path}");
    }
}

internal sealed record GitIndexEntry(string Mode, string ObjectId);
