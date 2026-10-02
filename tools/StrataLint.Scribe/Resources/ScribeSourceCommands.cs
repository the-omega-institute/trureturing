using System.Buffers;
using System.Security.Cryptography;
using System.Text;

namespace StrataLint.Scribe;

internal static class ScribeSourceCommands
{
    internal const string Usage = "usage: resources verify-source --source-commit <commit> --commit-from <file> --tree-from <file>";
    private const int MaximumReportedMismatches = 20;
    private const int HashBufferSize = 64 * 1024;

    internal static int Run(IReadOnlyList<string> arguments, string workingDirectory,
        Func<string> repositoryRoot, TextWriter output, TextWriter error)
    {
        var options = ParseOptions(arguments);
        if (options is null)
        {
            error.WriteLine(Usage);
            return 2;
        }

        try
        {
            var sourceCommit = options["--source-commit"];
            var commitPath = Path.GetFullPath(options["--commit-from"], workingDirectory);
            string rootTreeId;
            try
            {
                using var commit = File.OpenRead(commitPath);
                var actualCommit = ObjectId(commit, "commit", sourceCommit.Length);
                if (actualCommit != sourceCommit)
                {
                    error.WriteLine($"SourceCommitMismatch: expected={sourceCommit} actual={actualCommit}");
                    return 1;
                }
                commit.Position = 0;
                rootTreeId = ReadRootTreeId(commit, sourceCommit.Length);
            }
            catch (Exception exception) when (exception is IOException or UnauthorizedAccessException)
            {
                error.WriteLine($"SourceCommitReadFailed: {exception.Message}");
                return 2;
            }

            var root = Path.GetFullPath(repositoryRoot());
            var treePath = Path.GetFullPath(options["--tree-from"], workingDirectory);
            var bytes = File.ReadAllBytes(treePath);
            var entries = Parse(bytes, sourceCommit.Length);
            foreach (var entry in entries)
            {
                if (entry.Type == "blob" && entry.Mode is "100644" or "100755" or "120000") continue;
                error.WriteLine($"UnsupportedSourceEntry: {entry.Path} ({entry.Mode} {entry.Type})");
                return 1;
            }
            var actualTree = RebuildTree(entries, sourceCommit.Length);
            if (actualTree != rootTreeId)
            {
                error.WriteLine($"SourceRootTreeMismatch: expected={rootTreeId} actual={actualTree}");
                return 1;
            }
            var mismatches = 0;
            foreach (var entry in entries)
            {
                var path = Path.Combine(root, entry.Path.Replace('/', Path.DirectorySeparatorChar));
                var mismatch = entry.Mode switch
                {
                    "100644" or "100755" => VerifyFile(path, entry.Path, entry.ObjectId),
                    "120000" => VerifyLink(path, entry.Path, entry.ObjectId),
                    _ => $"UnsupportedSourceEntry: {entry.Path} ({entry.Mode} {entry.Type})",
                };
                if (mismatch is not null)
                {
                    mismatches++;
                    if (mismatches <= MaximumReportedMismatches) error.WriteLine(mismatch);
                }
            }

            if (mismatches != 0)
            {
                error.WriteLine($"SourceContentSummary: entries={entries.Count} mismatches={mismatches}");
                return 1;
            }

            output.WriteLine($"resources verify-source: entries={entries.Count}");
            return 0;
        }
        catch (InvalidDataException exception)
        {
            error.WriteLine(exception.Message);
            return 2;
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or ArgumentException or FormatException)
        {
            error.WriteLine($"SourceTreeReadFailed: {exception.Message}");
            return 2;
        }
    }

    private static Dictionary<string, string>? ParseOptions(IReadOnlyList<string> arguments)
    {
        if (arguments.Count != 8 || arguments[1] != "verify-source") return null;
        var options = new Dictionary<string, string>(StringComparer.Ordinal);
        for (var index = 2; index < arguments.Count; index += 2)
        {
            if (arguments[index] is not ("--source-commit" or "--commit-from" or "--tree-from")
                || string.IsNullOrWhiteSpace(arguments[index + 1])
                || !options.TryAdd(arguments[index], arguments[index + 1])) return null;
        }
        return IsObjectId(options["--source-commit"], options["--source-commit"].Length) ? options : null;
    }

    private static string ReadRootTreeId(Stream commit, int objectIdLength)
    {
        var firstLine = new byte[objectIdLength + 6];
        var count = 0;
        while (count < firstLine.Length)
        {
            var read = commit.Read(firstLine.AsSpan(count));
            if (read == 0) break;
            count += read;
        }
        if (count != firstLine.Length || !firstLine.AsSpan(0, 5).SequenceEqual("tree "u8)
            || firstLine[^1] != '\n')
            throw new InvalidDataException("InvalidSourceCommit: first line must be tree <object id>");
        var treeId = Encoding.ASCII.GetString(firstLine, 5, objectIdLength);
        if (!IsObjectId(treeId, objectIdLength))
            throw new InvalidDataException("InvalidSourceCommit: invalid root tree object id");
        return treeId;
    }

    private static string? VerifyFile(string path, string displayPath, string expected)
    {
        if (new FileInfo(path).LinkTarget is not null)
            return $"SourceTypeMismatch: {displayPath} (expected regular file)";
        if (Directory.Exists(path))
            return $"SourceTypeMismatch: {displayPath} (expected regular file)";
        if (File.Exists(path) is false)
            return $"MissingSourceEntry: {displayPath}";
        if (File.GetAttributes(path).HasFlag(FileAttributes.ReparsePoint))
            return $"SourceTypeMismatch: {displayPath} (expected regular file)";
        using var content = File.OpenRead(path);
        return ObjectId(content, "blob", expected.Length) == expected
            ? null
            : $"SourceContentMismatch: {displayPath}";
    }

    private static string? VerifyLink(string path, string displayPath, string expected)
    {
        var target = new FileInfo(path).LinkTarget;
        if (target is null && File.Exists(path) is false && Directory.Exists(path) is false)
            return $"MissingSourceEntry: {displayPath}";
        return target is null
            ? $"SourceTypeMismatch: {displayPath} (expected symbolic link)"
            : ObjectId(Encoding.UTF8.GetBytes(target), expected.Length) == expected
                ? null
                : $"SourceContentMismatch: {displayPath}";
    }

    private static string ObjectId(ReadOnlySpan<byte> content, int objectIdLength)
    {
        using var hash = StartObjectHash("blob", content.Length, objectIdLength);
        hash.AppendData(content);
        return Convert.ToHexStringLower(hash.GetHashAndReset());
    }

    private static string ObjectId(Stream content, string kind, int objectIdLength)
    {
        using var hash = StartObjectHash(kind, content.Length, objectIdLength);
        var buffer = ArrayPool<byte>.Shared.Rent(HashBufferSize);
        try
        {
            int count;
            while ((count = content.Read(buffer, 0, HashBufferSize)) != 0)
                hash.AppendData(buffer.AsSpan(0, count));
            return Convert.ToHexStringLower(hash.GetHashAndReset());
        }
        finally
        {
            ArrayPool<byte>.Shared.Return(buffer);
        }
    }

    private static IncrementalHash StartObjectHash(string kind, long length, int objectIdLength)
    {
        var hash = IncrementalHash.CreateHash(objectIdLength == 40 ? HashAlgorithmName.SHA1 : HashAlgorithmName.SHA256);
        hash.AppendData(Encoding.ASCII.GetBytes(FormattableString.Invariant($"{kind} {length}\0")));
        return hash;
    }

    private static string RebuildTree(IEnumerable<TreeEntry> entries, int objectIdLength)
    {
        var root = new TreeNode();
        foreach (var entry in entries)
        {
            var components = entry.Path.Split('/');
            var node = root;
            foreach (var component in components[..^1])
            {
                if (node.Files.ContainsKey(component))
                    throw new InvalidDataException($"InvalidSourceTree: file/directory collision {entry.Path}");
                if (!node.Directories.TryGetValue(component, out var directory))
                {
                    directory = new TreeNode();
                    node.Directories.Add(component, directory);
                }
                node = directory;
            }
            if (node.Directories.ContainsKey(components[^1]))
                throw new InvalidDataException($"InvalidSourceTree: file/directory collision {entry.Path}");
            node.Files.Add(components[^1], entry);
        }
        return TreeObjectId(root, objectIdLength);
    }

    private static string TreeObjectId(TreeNode node, int objectIdLength)
    {
        var entries = new List<EncodedTreeEntry>();
        foreach (var (name, directory) in node.Directories)
            entries.Add(EncodeTreeEntry("40000", name, TreeObjectId(directory, objectIdLength), true));
        foreach (var (name, entry) in node.Files)
            entries.Add(EncodeTreeEntry(entry.Mode, name, entry.ObjectId, false));
        entries.Sort(static (left, right) => left.SortName.AsSpan().SequenceCompareTo(right.SortName));
        var length = entries.Sum(entry => (long)entry.Header.Length + entry.ObjectId.Length);
        using var hash = StartObjectHash("tree", length, objectIdLength);
        foreach (var entry in entries)
        {
            hash.AppendData(entry.Header);
            hash.AppendData(entry.ObjectId);
        }
        return Convert.ToHexStringLower(hash.GetHashAndReset());
    }

    private static EncodedTreeEntry EncodeTreeEntry(string mode, string name, string objectId, bool directory) =>
        new(Encoding.UTF8.GetBytes($"{mode} {name}\0"), Convert.FromHexString(objectId),
            Encoding.UTF8.GetBytes(name + (directory ? "/" : "")));

    private static List<TreeEntry> Parse(ReadOnlySpan<byte> bytes, int objectIdLength)
    {
        if (!bytes.IsEmpty && bytes[^1] != 0)
            throw new InvalidDataException("InvalidSourceTree: entries must be NUL separated");
        var entries = new List<TreeEntry>();
        var seen = new HashSet<string>(StringComparer.Ordinal);
        var start = 0;
        while (start < bytes.Length)
        {
            var end = bytes[start..].IndexOf((byte)0);
            if (end < 0) throw new InvalidDataException("InvalidSourceTree: entries must be NUL separated");
            var record = bytes.Slice(start, end);
            start += end + 1;
            if (record.IsEmpty) throw new InvalidDataException("InvalidSourceTree: empty entry");
            var text = Decode(record);
            var tab = text.IndexOf('\t');
            if (tab <= 0 || tab == text.Length - 1)
                throw new InvalidDataException("InvalidSourceTree: each entry requires metadata and path");
            var metadata = text[..tab];
            var path = text[(tab + 1)..];
            var fields = metadata.Split(' ', StringSplitOptions.None);
            if (fields.Length != 3 || fields.Any(string.IsNullOrEmpty)
                || fields[1] is not ("blob" or "commit" or "tree"))
                throw new InvalidDataException($"InvalidSourceTree: {text}");
            if (!IsObjectId(fields[2], objectIdLength))
                throw new InvalidDataException($"InvalidSourceTree: object id for {path}");
            ValidatePath(path);
            if (!seen.Add(path)) throw new InvalidDataException($"InvalidSourceTree: duplicate path {path}");
            entries.Add(new TreeEntry(fields[0], fields[1], fields[2], path));
        }
        return entries;
    }

    private static bool IsHex(char value) => value is >= '0' and <= '9' or >= 'a' and <= 'f';

    private static bool IsObjectId(string value, int length) =>
        length is 40 or 64 && value.Length == length && value.All(IsHex);

    private static string Decode(ReadOnlySpan<byte> bytes)
    {
        try { return new UTF8Encoding(false, true).GetString(bytes); }
        catch (DecoderFallbackException exception) { throw new InvalidDataException("InvalidSourceTree: invalid UTF-8", exception); }
    }

    private static void ValidatePath(string path)
    {
        if (path.Length == 0 || path.Contains('\\') || Path.IsPathRooted(path)
            || path.StartsWith("//", StringComparison.Ordinal)
            || path.StartsWith("\\", StringComparison.Ordinal)
            || path.Split('/').Any(static part => part is "" or "." or "..")
            || (path.Length >= 2 && path[1] == ':'))
            throw new InvalidDataException($"InvalidSourceTree: invalid path {path}");
    }

    private readonly record struct TreeEntry(string Mode, string Type, string ObjectId, string Path);
    private readonly record struct EncodedTreeEntry(byte[] Header, byte[] ObjectId, byte[] SortName);

    private sealed class TreeNode
    {
        internal Dictionary<string, TreeNode> Directories { get; } = new(StringComparer.Ordinal);
        internal Dictionary<string, TreeEntry> Files { get; } = new(StringComparer.Ordinal);
    }
}
