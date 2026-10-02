using System.Buffers;
using System.Security.Cryptography;
using System.Text;

namespace StrataLint.Scribe;

internal static class ScribeSourceCommands
{
    internal const string Usage = "usage: resources verify-source --tree-from <file>";
    private const int MaximumReportedMismatches = 20;

    internal static int Run(IReadOnlyList<string> arguments, string workingDirectory,
        Func<string> repositoryRoot, TextWriter output, TextWriter error)
    {
        if (arguments.Count != 4 || arguments[1] != "verify-source"
            || arguments[2] != "--tree-from" || string.IsNullOrWhiteSpace(arguments[3]))
        {
            error.WriteLine(Usage);
            return 2;
        }

        try
        {
            var root = Path.GetFullPath(repositoryRoot());
            var treePath = Path.GetFullPath(arguments[3], workingDirectory);
            var bytes = File.ReadAllBytes(treePath);
            var entries = Parse(bytes);
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
        return ObjectId(File.ReadAllBytes(path), expected.Length) == expected
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
        var header = Encoding.UTF8.GetBytes($"blob {content.Length}\0");
        var input = ArrayPool<byte>.Shared.Rent(header.Length + content.Length);
        try
        {
            header.CopyTo(input);
            content.CopyTo(input.AsSpan(header.Length));
            var digest = objectIdLength == 40
                ? SHA1.HashData(input.AsSpan(0, header.Length + content.Length))
                : SHA256.HashData(input.AsSpan(0, header.Length + content.Length));
            return Convert.ToHexStringLower(digest);
        }
        finally
        {
            ArrayPool<byte>.Shared.Return(input);
        }
    }

    private static List<TreeEntry> Parse(ReadOnlySpan<byte> bytes)
    {
        if (bytes.IsEmpty || bytes[^1] != 0)
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
            if (fields[2].Length is not (40 or 64) || fields[2].Any(static c => !IsHex(c)))
                throw new InvalidDataException($"InvalidSourceTree: object id for {path}");
            ValidatePath(path);
            if (!seen.Add(path)) throw new InvalidDataException($"InvalidSourceTree: duplicate path {path}");
            entries.Add(new TreeEntry(fields[0], fields[1], fields[2], path));
        }
        return entries;
    }

    private static bool IsHex(char value) => value is >= '0' and <= '9' or >= 'a' and <= 'f';

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
}
