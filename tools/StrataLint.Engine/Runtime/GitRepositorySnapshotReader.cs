using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal static class GitRepositorySnapshotReader
{
    private const int MaximumGitOutputBytes = 64 * 1024 * 1024;
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static RawRepositorySnapshot ReadCurrent(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var root = Path.GetFullPath(repositoryRoot);
        var tracked = ParseIndex(Git(root, "ls-files", "--stage", "-z"));
        var paths = tracked.Keys
            .Concat(ParseNulStrings(Git(
                root,
                "ls-files",
                "--others",
                "--exclude-standard",
                "-z")))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal);
        var entries = ImmutableArray.CreateBuilder<RawRepositoryEntry>();
        foreach (var path in paths)
        {
            if (!RepoPath.TryCreate(path, out _))
            {
                throw new InvalidOperationException($"git emitted an invalid repository path: {path}");
            }

            if (tracked.TryGetValue(path, out var mode) && mode is not ("100644" or "100755"))
            {
                throw new InvalidOperationException(
                    $"non-regular repository entry {path} has git mode {mode}");
            }

            var fullPath = Path.Combine(root, path);
            var info = new FileInfo(fullPath);
            if (!info.Exists)
            {
                continue;
            }

            if (info.LinkTarget is not null || (info.Attributes & FileAttributes.ReparsePoint) != 0)
            {
                throw new InvalidOperationException(
                    $"non-regular repository entry {path} is not a plain file");
            }

            entries.Add(new RawRepositoryEntry(
                path,
                ImmutableArray.CreateRange(File.ReadAllBytes(fullPath))));
        }

        return RawRepositorySnapshot.Create(entries);
    }

    internal static RawRepositorySnapshot ReadRevision(string repositoryRoot, string revision)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentException.ThrowIfNullOrWhiteSpace(revision);
        var root = Path.GetFullPath(repositoryRoot);
        return ReadRevision(
            revision,
            (arguments, maximumOutputBytes, standardInput) => GitRaw(
                root,
                arguments,
                maximumOutputBytes,
                standardInput));
    }

    internal static RawRepositorySnapshot ReadRevision(
        string revision,
        Func<IReadOnlyList<string>, int, ReadOnlyMemory<byte>, ProcessOutput> runGit)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(revision);
        ArgumentNullException.ThrowIfNull(runGit);
        var treeResult = runGit(
            ["ls-tree", "-r", "-l", "-z", revision],
            MaximumGitOutputBytes,
            default);
        EnsureSuccess(treeResult);
        var tree = ParseTree(treeResult.StandardOutput).ToArray();
        foreach (var entry in tree)
        {
            if (entry.Mode is not ("100644" or "100755")
                || entry.ObjectType != "blob"
                || entry.Size is null)
            {
                throw new InvalidOperationException(
                    $"protected base has non-regular entry {entry.Path} ({entry.Mode} {entry.ObjectType})");
            }
        }

        var objects = tree
            .DistinctBy(static entry => entry.ObjectId, StringComparer.Ordinal)
            .ToArray();
        if (objects.Length == 0)
        {
            return RawRepositorySnapshot.Create([]);
        }

        var input = StrictUtf8.GetBytes(
            string.Concat(objects.Select(static entry => entry.ObjectId + "\n")));
        var objectResult = runGit(
            ["cat-file", "--batch"],
            BatchOutputLimit(objects),
            input);
        EnsureSuccess(objectResult);
        var blobs = ParseBatchObjects(objects, objectResult.StandardOutput);
        return RawRepositorySnapshot.Create(tree.Select(entry => new RawRepositoryEntry(
            entry.Path,
            blobs[entry.ObjectId],
            (entry.ObjectId.Length == 40 ? "git-sha1:" : "git-sha256:") + entry.ObjectId)));
    }

    private static byte[] Git(string root, params string[] arguments)
    {
        var result = GitRaw(root, arguments, MaximumGitOutputBytes, default);
        EnsureSuccess(result);
        return result.StandardOutput;
    }

    private static ProcessOutput GitRaw(
        string root,
        IReadOnlyList<string> arguments,
        int maximumOutputBytes,
        ReadOnlyMemory<byte> standardInput) =>
        BoundedProcessRunner.Run(
            "git",
            arguments,
            root,
            TimeSpan.FromSeconds(120),
            maximumOutputBytes,
            standardInput);

    private static void EnsureSuccess(ProcessOutput result)
    {
        if (result.ExitCode == 0)
        {
            return;
        }

        throw new InvalidOperationException(
            StrictUtf8.GetString(result.StandardError).Trim() is { Length: > 0 } error
                ? error
                : "git command failed");
    }

    private static int BatchOutputLimit(IEnumerable<GitRepositoryTreeEntry> entries)
    {
        long maximum = 0;
        foreach (var entry in entries)
        {
            var size = entry.Size!.Value;
            var overhead = entry.ObjectId.Length + 64;
            if (size > int.MaxValue || maximum > int.MaxValue - size - overhead)
            {
                throw new InvalidOperationException("revision snapshot exceeds the supported batch size");
            }

            maximum += size + overhead;
        }

        return (int)maximum;
    }

    private static IReadOnlyDictionary<string, ImmutableArray<byte>> ParseBatchObjects(
        IReadOnlyList<GitRepositoryTreeEntry> expected,
        byte[] output)
    {
        var blobs = new Dictionary<string, ImmutableArray<byte>>(StringComparer.Ordinal);
        var offset = 0;
        foreach (var entry in expected)
        {
            var headerEnd = Array.IndexOf(output, (byte)'\n', offset);
            if (headerEnd < offset)
            {
                throw InvalidBatchOutput(entry.ObjectId);
            }

            var header = StrictUtf8.GetString(output.AsSpan(offset, headerEnd - offset));
            var fields = header.Split(' ', StringSplitOptions.RemoveEmptyEntries);
            if (fields.Length != 3
                || !string.Equals(fields[0], entry.ObjectId, StringComparison.Ordinal)
                || !string.Equals(fields[1], "blob", StringComparison.Ordinal)
                || !long.TryParse(
                    fields[2],
                    System.Globalization.NumberStyles.None,
                    System.Globalization.CultureInfo.InvariantCulture,
                    out var size)
                || size != entry.Size
                || size > int.MaxValue)
            {
                throw InvalidBatchOutput(entry.ObjectId);
            }

            var contentStart = headerEnd + 1;
            if (size > output.Length - contentStart - 1)
            {
                throw InvalidBatchOutput(entry.ObjectId);
            }

            var contentEnd = contentStart + (int)size;
            if (output[contentEnd] != (byte)'\n')
            {
                throw InvalidBatchOutput(entry.ObjectId);
            }

            blobs.Add(
                entry.ObjectId,
                ImmutableArray.CreateRange(output.AsSpan(contentStart, (int)size).ToArray()));
            offset = contentEnd + 1;
        }

        if (offset != output.Length)
        {
            throw new InvalidOperationException("git cat-file --batch emitted trailing data");
        }

        return blobs;
    }

    private static InvalidOperationException InvalidBatchOutput(string objectId) =>
        new($"git cat-file --batch emitted invalid data for object {objectId}");

    internal static IEnumerable<GitRepositoryTreeEntry> ParseTree(byte[] bytes)
    {
        foreach (var entry in SplitNul(bytes))
        {
            var tab = Array.IndexOf(entry, (byte)'\t');
            if (tab <= 0) throw new InvalidOperationException("git tree emitted invalid metadata");
            var metadata = StrictUtf8.GetString(entry.AsSpan(0, tab))
                .Split(' ', StringSplitOptions.RemoveEmptyEntries);
            var path = StrictUtf8.GetString(entry.AsSpan(tab + 1));
            if (metadata.Length is not (3 or 4) || !RepoPath.TryCreate(path, out _))
            {
                throw new InvalidOperationException($"git tree emitted invalid entry: {path}");
            }

            long? size = null;
            if (metadata.Length == 4 && metadata[3] != "-")
            {
                if (!long.TryParse(
                        metadata[3],
                        System.Globalization.NumberStyles.None,
                        System.Globalization.CultureInfo.InvariantCulture,
                        out var parsedSize))
                {
                    throw new InvalidOperationException($"git tree emitted invalid entry: {path}");
                }

                size = parsedSize;
            }

            yield return new GitRepositoryTreeEntry(metadata[0], metadata[1], metadata[2], path, size);
        }
    }

    private static Dictionary<string, string> ParseIndex(byte[] bytes)
    {
        var result = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var entry in SplitNul(bytes))
        {
            var tab = Array.IndexOf(entry, (byte)'\t');
            if (tab <= 0)
            {
                throw new InvalidOperationException("git index emitted invalid metadata");
            }

            var metadata = StrictUtf8.GetString(entry.AsSpan(0, tab)).Split(' ');
            var path = StrictUtf8.GetString(entry.AsSpan(tab + 1));
            if (metadata.Length != 3 || metadata[2] != "0" || !result.TryAdd(path, metadata[0]))
            {
                throw new InvalidOperationException(
                    $"unmerged or duplicate repository entry: {path}");
            }
        }

        return result;
    }

    private static IEnumerable<string> ParseNulStrings(byte[] bytes) =>
        SplitNul(bytes).Select(static item => StrictUtf8.GetString(item));

    private static IEnumerable<byte[]> SplitNul(byte[] bytes)
    {
        var start = 0;
        for (var index = 0; index <= bytes.Length; index++)
        {
            if (index != bytes.Length && bytes[index] != 0)
            {
                continue;
            }

            if (index > start)
            {
                yield return bytes[start..index];
            }

            start = index + 1;
        }
    }

}

internal sealed record GitRepositoryTreeEntry(
    string Mode,
    string ObjectType,
    string ObjectId,
    string Path,
    long? Size);
