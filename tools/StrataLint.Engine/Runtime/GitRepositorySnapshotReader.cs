using System.Collections.Immutable;
using System.Runtime.ExceptionServices;
using System.Runtime.InteropServices;
using System.Text;

namespace StrataLint.Engine;

internal static class GitRepositorySnapshotReader
{
    private const int MaximumGitOutputBytes = 64 * 1024 * 1024;
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    // readContents only projects regular bodies, never entries or link bytes.
    // FILEMAP policy bytes are retained for the same structural validation and
    // effective inventory as the full reader. pathspecs bound enumeration itself:
    // a scoped reader never probes paths outside them, so its cost follows its
    // inputs rather than the repository size. Include the policy documents in
    // the scope when links inside it must be validated.
    internal static RawRepositorySnapshot ReadCurrent(string repositoryRoot, Func<string, bool>? include = null,
        Func<string, bool>? readContents = null, IReadOnlyList<string>? pathspecs = null)
        => ReadCurrentCore(repositoryRoot, include, null, readContents, pathspecs);

    // Visit every file while retaining only the bytes needed for the same link
    // validation as a full snapshot. Identity consumers need the complete path
    // inventory, but do not need all file bodies alive at once.
    internal static ImmutableArray<RepositoryPathInventoryEntry> VisitCurrent(string repositoryRoot, Action<RawRepositoryEntry> visit)
    {
        ArgumentNullException.ThrowIfNull(visit);
        return ReadCurrentCore(repositoryRoot, null, visit).PathInventory;
    }

    private static RawRepositorySnapshot ReadCurrentCore(string repositoryRoot, Func<string, bool>? include,
        Action<RawRepositoryEntry>? visit, Func<string, bool>? readContents = null,
        IReadOnlyList<string>? pathspecs = null)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var root = Path.GetFullPath(repositoryRoot);
        string[] scope = pathspecs is null ? [] : ["--", .. pathspecs];
        var tracked = ParseIndex(Git(root, ["ls-files", "--stage", "-z", .. scope]));
        var paths = tracked.Keys
            .Concat(ParseNulStrings(Git(root, ["ls-files", "--others", "--exclude-standard", "-z", .. scope])))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        var entries = ImmutableArray.CreateBuilder<RawRepositoryEntry>();
        var inventory = ImmutableArray.CreateBuilder<RepositoryPathInventoryEntry>();
        var links = new HashSet<string>(StringComparer.Ordinal);
        var inspectedDirectories = new HashSet<string>(StringComparer.Ordinal);
        void Retain(RawRepositoryEntry entry, bool link = false)
        {
            visit?.Invoke(entry);
            entries.Add(visit is null || link || FileMapDocuments.IsPolicyPath(entry.Path)
                ? entry : entry with { Bytes = [] });
        }
        for (var offset = 0; offset < paths.Length; offset += ProbeWindowPaths)
        {
            var probes = new PathProbe[Math.Min(ProbeWindowPaths, paths.Length - offset)];
            // Path validation and ancestor inspection keep path order; each failure is
            // raised when its own path is reached, exactly as a sequential read would.
            for (var index = 0; index < probes.Length; index++)
            {
                var path = paths[offset + index];
                var probe = probes[index] = new PathProbe(path, Path.Combine(root, path));
                try
                {
                    if (!RepoPath.TryCreate(path, out _))
                    {
                        throw new InvalidOperationException($"git emitted an invalid repository path: {path}");
                    }

                    if (tracked.TryGetValue(path, out var mode) && !IsSupportedMode(mode))
                    {
                        throw new InvalidOperationException(
                            $"non-regular repository entry {path} has git mode {mode}");
                    }

                    FileMapSymlinkPolicy.RequirePlainAncestors(root, path, inspectedDirectories);
                    probe.Included = include is null || include(path);
                    probe.WantsContents = readContents is null || readContents(path) || FileMapDocuments.IsPolicyPath(path);
                }
                catch (Exception exception)
                {
                    probe.Failure = ExceptionDispatchInfo.Capture(exception);
                }
            }

            // Independent lstat and body reads run concurrently; results stay indexed.
            if (probes.Length >= ParallelProbeThreshold)
                Parallel.ForEach(probes, static probe => probe.Load());
            else
                foreach (var probe in probes) probe.Load();

            foreach (var probe in probes)
            {
                probe.Failure?.Throw();
                var path = probe.Path;
                var indexMode = tracked.TryGetValue(path, out var indexedMode) ? indexedMode : null;
                if (probe.LinkTarget is { } target)
                {
                    var linkBytes = ReadLinkBytes(root, probe.FullPath, target);
                    inventory.Add(new(path, indexMode, "symlink", "120000", StrictUtf8.GetString(linkBytes)));
                    if (!probe.Included) continue;
                    links.Add(path);
                    Retain(new RawRepositoryEntry(path, ImmutableArray.CreateRange(linkBytes)), link: true);
                    continue;
                }

                if (probe.Directory)
                    throw new InvalidOperationException($"non-regular repository entry {path} is a directory");
                if (!probe.Exists)
                {
                    inventory.Add(new(path, indexMode, "absent", null, null));
                    continue;
                }

                if (probe.Irregular)
                {
                    throw new InvalidOperationException(
                        $"non-regular repository entry {path} is not a plain file");
                }

                inventory.Add(new(path, indexMode, "regular", probe.Executable ? "100755" : "100644", null));
                if (!probe.Included) continue;
                probe.BodyFailure?.Throw();
                // The fresh read buffer has no mutable alias; the snapshot owns it.
                Retain(new RawRepositoryEntry(path, probe.Body is { } body
                    ? ImmutableCollectionsMarshal.AsImmutableArray(body) : []));
            }
        }

        FileMapSymlinkPolicy.ValidateSnapshot(entries, links, paths, path =>
        {
            FileMapSymlinkPolicy.RequirePlainAncestors(root, path, inspectedDirectories);
            var info = new FileInfo(Path.Combine(root, path));
            return info.Exists || Directory.Exists(info.FullName) || info.LinkTarget is not null;
        });
        return RawRepositorySnapshot.Create(entries, inventory.ToImmutable());
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
            if (!IsSupportedMode(entry.Mode)
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
        var entries = tree.Select(entry => new RawRepositoryEntry(
            entry.Path,
            blobs[entry.ObjectId],
            (entry.ObjectId.Length == 40 ? "git-sha1:" : "git-sha256:") + entry.ObjectId)).ToArray();
        FileMapSymlinkPolicy.ValidateSnapshot(entries,
            tree.Where(static entry => entry.Mode == "120000").Select(entry => entry.Path).ToHashSet(StringComparer.Ordinal),
            tree.Select(entry => entry.Path).ToArray());
        return RawRepositorySnapshot.Create(entries);
    }

    // policy-override (#11124): bounds how many file bodies a visiting reader holds at
    // once; not derived from host capacity. Exit: a measured memory/throughput receipt.
    internal const int ProbeWindowPaths = 4096;

    // Below this a window is read inline; tiny repositories gain nothing from workers.
    internal const int ParallelProbeThreshold = 64;

    private sealed class PathProbe(string path, string fullPath)
    {
        internal string Path { get; } = path;
        internal string FullPath { get; } = fullPath;
        internal bool Included { get; set; }
        internal bool WantsContents { get; set; }
        internal ExceptionDispatchInfo? Failure { get; set; }
        internal ExceptionDispatchInfo? BodyFailure { get; private set; }
        internal string? LinkTarget { get; private set; }
        internal bool Directory { get; private set; }
        internal bool Exists { get; private set; }
        internal bool Irregular { get; private set; }
        internal bool Executable { get; private set; }
        internal byte[]? Body { get; private set; }

        // Same lstat-cached FileInfo sequence as the sequential reader; the body read
        // follows its own lstat so each file is observed once, in one place.
        internal void Load()
        {
            if (Failure is not null) return;
            try
            {
                var info = new FileInfo(FullPath);
                var attributes = info.Attributes;
                var present = attributes != (FileAttributes)(-1);
                if (present && (attributes & FileAttributes.ReparsePoint) != 0 && info.LinkTarget is { } target)
                {
                    LinkTarget = target;
                    return;
                }

                if (present && (attributes & FileAttributes.Directory) != 0)
                {
                    Directory = true;
                    return;
                }

                Exists = info.Exists;
                if (!Exists) return;
                if ((attributes & (FileAttributes.ReparsePoint | FileAttributes.Device)) != 0)
                {
                    Irregular = true;
                    return;
                }

                Executable = !OperatingSystem.IsWindows() && (info.UnixFileMode
                    & (UnixFileMode.UserExecute | UnixFileMode.GroupExecute | UnixFileMode.OtherExecute)) != 0;
                if (!Included || !WantsContents) return;
                try { Body = File.ReadAllBytes(FullPath); }
                catch (Exception exception) { BodyFailure = ExceptionDispatchInfo.Capture(exception); }
            }
            catch (Exception exception)
            {
                Failure = ExceptionDispatchInfo.Capture(exception);
            }
        }
    }

    private static bool IsSupportedMode(string mode) => mode is "100644" or "100755" or "120000";

    private static byte[] ReadLinkBytes(string root, string fullPath, string target)
    {
        // Unix link targets are arbitrary bytes. FileInfo.LinkTarget replaces invalid
        // UTF-8 before returning a string, so re-encoding it would fabricate identity.
        // Windows reparse points store UTF-16; strict encoding preserves that contract.
        if (OperatingSystem.IsWindows()) return StrictUtf8.GetBytes(target);
        var result = BoundedProcessRunner.Run("readlink", [fullPath], root,
            BoundedProcessRunner.HangDetectionBudget, 64 * 1024);
        EnsureSuccess(result);
        var output = result.StandardOutput;
        if (output.Length == 0 || output[^1] != (byte)'\n')
            throw new InvalidOperationException($"readlink emitted invalid output for {fullPath}");
        var bytes = output[..^1]; // readlink appends one LF after the native target bytes.
        try
        {
            _ = StrictUtf8.GetString(bytes);
        }
        catch (DecoderFallbackException exception)
        {
            throw new InvalidOperationException($"non-regular repository entry {fullPath}: symlink target must be strict UTF-8", exception);
        }
        return bytes;
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
