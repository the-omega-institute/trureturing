using System.Collections.Immutable;
using System.Text;
using Tomlyn;
using Tomlyn.Model;

namespace StrataLint.Engine;

internal sealed record FileMapSymlink(string Path, string Target, string Kind, string ResolvedTarget);

// The strict FILEMAP loader and Git snapshot reader share this declaration contract.
// A link is an alias entry containing target bytes; its referent has its own paths.
internal static class FileMapSymlinkPolicy
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static FileMapSymlink? ParseEntry(TomlTable table, string location)
    {
        if (!table.TryGetValue("symlink", out var raw)) return null;
        if (raw is not TomlTable link || link.Count != 2
            || !link.TryGetValue("target", out var rawTarget) || rawTarget is not string target
            || !link.TryGetValue("kind", out var rawKind) || rawKind is not ("file" or "directory")
            || !table.TryGetValue("pattern", out var rawPath) || rawPath is not string path
            || !IsLiteralPath(path)
            || !table.TryGetValue("runtime_disposition", out var disposition) || disposition is not "committed-source")
        {
            throw Invalid(location, "symlink requires a literal committed-source path and exactly target and kind (file or directory)");
        }

        var resolved = Resolve(path, target, location);
        if (IsReserved(path) || IsReserved(resolved)
            || path == AdmissionPlanePolicy.FileMapPath
            || AdmissionPlanePolicy.FileMapPath.StartsWith(path + "/", StringComparison.Ordinal)
            || resolved == path || resolved.StartsWith(path + "/", StringComparison.Ordinal)
            || (rawKind is "directory" && path.StartsWith(resolved + "/", StringComparison.Ordinal)))
        {
            throw Invalid(location, "symlink cannot alias Git/cache state, FILEMAP, itself or an ancestor directory");
        }

        return new FileMapSymlink(path, target, (string)rawKind, resolved);
    }

    internal static ImmutableArray<FileMapSymlink> Parse(ReadOnlySpan<byte> bytes, string location)
    {
        TomlTable root;
        try
        {
            if (bytes.IsEmpty || bytes[^1] != (byte)'\n' || bytes.Contains((byte)'\r')
                || bytes.StartsWith(new byte[] { 0xEF, 0xBB, 0xBF }))
                throw Invalid(location, "bytes must be strict UTF-8 without BOM/CR and end in LF");
            root = TomlSerializer.Deserialize<TomlTable>(StrictUtf8.GetString(bytes))
                ?? throw Invalid(location, "TOML decoded to null");
        }
        catch (Exception exception) when (exception is TomlException or DecoderFallbackException)
        {
            throw new FileMapParseException(location, "invalid UTF-8 TOML", exception);
        }

        if (!root.TryGetValue("schema_version", out var version) || version is not 2L
            || !root.TryGetValue("files", out var rawFiles) || rawFiles is not TomlTableArray files)
            throw Invalid(location, "symlink declarations require schema_version 2 and files tables");

        var declarations = files.Select((table, index) => ParseEntry(table, $"{location}:files[{index}]"))
            .OfType<FileMapSymlink>().ToImmutableArray();
        var patterns = files.Select(table => table.TryGetValue("pattern", out var rawPattern) && rawPattern is string pattern
            ? FileMapGlob.Create(pattern)
            : throw Invalid(location, "file pattern must be a string")).ToArray();
        ValidateCoverage(declarations, path => patterns.Count(pattern => pattern.IsMatch(path)), location);
        return declarations;
    }

    internal static void ValidateCoverage(IEnumerable<FileMapSymlink> declarations, Func<string, int> matchCount, string location)
    {
        foreach (var declaration in declarations)
            if (matchCount(declaration.Path) != 1)
                throw Invalid(location, $"symlink path {declaration.Path} must match exactly one FILEMAP entry");
    }

    internal static void ValidateSnapshot(
        IReadOnlyCollection<RawRepositoryEntry> entries,
        IReadOnlySet<string> linkPaths,
        IReadOnlyCollection<string> discoveredPaths,
        Func<string, bool>? isPresent = null)
    {
        if (linkPaths.Count == 0) return;
        var byPath = entries.ToDictionary(entry => entry.Path, StringComparer.Ordinal);
        if (!byPath.TryGetValue(AdmissionPlanePolicy.FileMapPath, out var fileMap)
            || linkPaths.Contains(AdmissionPlanePolicy.FileMapPath))
            throw Rejected(AdmissionPlanePolicy.FileMapPath, "a plain FILEMAP must be present in the same snapshot");

        ImmutableArray<FileMapSymlink> declarations;
        try
        {
            declarations = Parse(fileMap.Bytes.AsSpan(), AdmissionPlanePolicy.FileMapPath);
        }
        catch (FormatException exception)
        {
            throw new InvalidOperationException("non-regular repository entry: " + exception.Message, exception);
        }

        foreach (var path in linkPaths)
        {
            var declaration = declarations.SingleOrDefault(item => item.Path == path);
            if (declaration is null || !byPath[path].Bytes.AsSpan().SequenceEqual(StrictUtf8.GetBytes(declaration.Target)))
                throw Rejected(path, "symlink target must exactly match its FILEMAP declaration");

            var target = declaration.ResolvedTarget;
            if (linkPaths.Any(link => target == link || target.StartsWith(link + "/", StringComparison.Ordinal)))
                throw Rejected(path, "symlink target must have no symlink ancestors or chains");

            if (declaration.Kind == "file")
            {
                if (!byPath.ContainsKey(target))
                    throw Rejected(path, "plain target file must be present in the same snapshot");
            }
            else
            {
                var prefix = target + "/";
                var members = discoveredPaths.Where(item => item.StartsWith(prefix, StringComparison.Ordinal)
                    && (byPath.ContainsKey(item) || isPresent?.Invoke(item) != false)).ToArray();
                if (byPath.ContainsKey(target) || members.Length == 0
                    || members.Any(member => !byPath.ContainsKey(member) || linkPaths.Contains(member)))
                    throw Rejected(path, "target directory must contain plain files, all present in the same snapshot");
            }
        }
    }

    // Inspect each physical ancestor before opening a tracked file. Git's index can
    // still list descendants of a directory replaced by a symlink in the worktree.
    internal static void RequirePlainAncestors(string root, string path, ISet<string> inspected)
    {
        var parts = path.Split('/');
        var parent = root;
        foreach (var part in parts.SkipLast(1))
        {
            parent = System.IO.Path.Combine(parent, part);
            if (!inspected.Add(parent)) continue;
            var info = new DirectoryInfo(parent);
            if (info.LinkTarget is not null || (info.Exists && (info.Attributes & FileAttributes.ReparsePoint) != 0))
                throw Rejected(path, "repository entry has a symlink ancestor");
        }
    }

    private static string Resolve(string path, string target, string location)
    {
        var parts = path.Split('/').SkipLast(1).ToList();
        var descending = false;
        foreach (var part in target.Split('/'))
        {
            if (part == ".." && !descending && parts.Count > 0)
                parts.RemoveAt(parts.Count - 1);
            else if (IsLiteralPath(part) && !part.Contains('/'))
            {
                parts.Add(part);
                descending = true;
            }
            else
                throw Invalid(location, "symlink target must be a canonical relative path within the repository");
        }
        if (parts.Count == 0)
            throw Invalid(location, "symlink cannot target the repository root");
        return string.Join('/', parts);
    }

    private static bool IsLiteralPath(string path) =>
        RepoPath.TryCreate(path, out _) && !path.Any(character => char.IsControl(character)
            || character is '*' or '?' or '[' or ']' or ':' || char.IsWhiteSpace(character));

    private static bool IsReserved(string path) => path.Split('/').Any(part =>
        part.Equals(".git", StringComparison.OrdinalIgnoreCase) || part.Equals(".lake", StringComparison.OrdinalIgnoreCase));

    private static FormatException Invalid(string location, string message) =>
        new FileMapParseException(location, message);

    private static InvalidOperationException Rejected(string path, string message) =>
        new($"non-regular repository entry {path}: {message}");
}
