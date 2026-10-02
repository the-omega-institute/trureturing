using System.Text;

namespace StrataLint.Scribe;

internal static class ScribeReleaseCommands
{
    private const string IdentityFile = "identity.json";
    private static readonly string[] Assets = [ScribeResourceBundle.ResourceName, IdentityFile, ScribeResourceBundle.FileName];

    internal static int Run(IReadOnlyList<string> arguments, string workingDirectory,
        Func<string> repositoryRoot, TextWriter output, TextWriter error)
    {
        try
        {
            var release = arguments[1] == "release";
            var options = Parse(arguments, release);
            var directory = Path.GetFullPath(options[release ? "--out" : "--dir"], workingDirectory);
            return release
                ? Release(repositoryRoot(), directory, options["--source-commit"], output, error)
                : Verify(directory, options, options.TryGetValue("--tree-from", out var treeFile)
                    ? ReadDefinitionPathsFromTree(Path.GetFullPath(treeFile, workingDirectory)) : null, output, error);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or ArgumentException or FormatException or InvalidOperationException)
        {
            error.WriteLine(exception.Message);
            if (exception is ArgumentException) error.WriteLine(ScribeResourceCommands.Usage);
            return 2;
        }
    }

    private static Dictionary<string, string> Parse(IReadOnlyList<string> arguments, bool release)
    {
        var options = new Dictionary<string, string>(StringComparer.Ordinal);
        var allowed = release ? new[] { "--source-commit", "--out" } : ["--dir", "--source-commit", "--total-sha256", "--tree-from"];
        if (arguments.Count < 4 || arguments.Count % 2 != 0)
            throw new ArgumentException("InvalidReleaseArguments: options require a name and value.");
        for (var index = 2; index < arguments.Count; index += 2)
        {
            if (!allowed.Contains(arguments[index], StringComparer.Ordinal)
                || string.IsNullOrWhiteSpace(arguments[index + 1])
                || !options.TryAdd(arguments[index], arguments[index + 1]))
                throw new ArgumentException("InvalidReleaseArguments: unknown, empty or duplicate option.");
        }
        if (!options.ContainsKey(release ? "--out" : "--dir")
            || release && !options.ContainsKey("--source-commit"))
            throw new ArgumentException("InvalidReleaseArguments: required option is missing.");
        if (options.TryGetValue("--source-commit", out var commit) && !ScribeReleaseIdentityCodec.IsHex(commit, 40))
            throw new ArgumentException("InvalidSourceCommit: requires 40 lowercase hexadecimal characters.");
        if (options.TryGetValue("--total-sha256", out var digest) && !ScribeReleaseIdentityCodec.IsHex(digest, 64))
            throw new ArgumentException("InvalidTotalSha256: requires 64 lowercase hexadecimal characters.");
        return options;
    }

    private static int Release(string root, string directory, string commit, TextWriter output, TextWriter error)
    {
        RequireEmptyTarget(directory);
        var staging = Directory.CreateTempSubdirectory("scribe-release-");
        try
        {
            var packPath = Path.Combine(staging.FullName, ScribeResourceBundle.ResourceName);
            var result = ScribeResourceScriptPacker.Write(root, packPath);
            if (!result.Failures.IsEmpty)
            {
                foreach (var failure in result.Failures) error.WriteLine(failure);
                return 1;
            }
            var manifest = result.Manifest!;
            var identity = new ScribeReleaseIdentity(ScribeReleaseIdentityCodec.SchemaName, commit,
                manifest.Version, manifest.EntryCount, manifest.TotalSha256);
            File.WriteAllBytes(Path.Combine(staging.FullName, IdentityFile), ScribeReleaseIdentityCodec.Encode(identity));
            File.WriteAllBytes(Path.Combine(staging.FullName, ScribeResourceBundle.FileName),
                ScribeResourceBundle.Write(File.ReadAllBytes(packPath)));
            Publish(staging.FullName, directory);
            output.WriteLine(Summary("release", identity));
            return 0;
        }
        finally { staging.Delete(recursive: true); }
    }

    private static void RequireEmptyTarget(string directory)
    {
        if (File.Exists(directory))
            throw new ArgumentException("InvalidReleaseDirectory: the target is a file.");
        if (Directory.Exists(directory) && Directory.EnumerateFileSystemEntries(directory).Any())
            throw new ArgumentException("ReleaseDirectoryNotEmpty: the target directory must be absent or empty.");
    }

    private static void Publish(string staging, string directory)
    {
        RequireEmptyTarget(directory);
        var existed = Directory.Exists(directory);
        var written = new List<string>();
        try
        {
            Directory.CreateDirectory(directory);
            foreach (var asset in Assets)
            {
                var target = Path.Combine(directory, asset);
                // CreateNew keeps an independently created file from being overwritten.
                using var destination = new FileStream(target, FileMode.CreateNew, FileAccess.Write);
                written.Add(target);
                using var source = File.OpenRead(Path.Combine(staging, asset));
                source.CopyTo(destination);
            }
        }
        catch
        {
            foreach (var path in written) File.Delete(path);
            if (!existed && Directory.Exists(directory) && !Directory.EnumerateFileSystemEntries(directory).Any())
                Directory.Delete(directory);
            throw;
        }
    }

    private static HashSet<string> ReadDefinitionPathsFromTree(string path)
    {
        var paths = new HashSet<string>(StringComparer.Ordinal);
        var bytes = File.ReadAllBytes(path);
        if (bytes.Length != 0 && bytes[^1] != 0)
            throw new ArgumentException("InvalidDefinitionTree: entries must be NUL separated.");
        var start = 0;
        while (start < bytes.Length)
        {
            var end = bytes.AsSpan(start).IndexOf((byte)0);
            if (end < 0) throw new ArgumentException("InvalidDefinitionTree: entries must be NUL separated.");
            var record = bytes.AsSpan(start, end);
            start += end + 1;
            var tab = record.IndexOf((byte)'\t');
            if (tab <= 0 || tab == record.Length - 1)
                throw new ArgumentException("InvalidDefinitionTree: each entry requires metadata and path.");
            string text;
            try { text = new System.Text.UTF8Encoding(false, true).GetString(record); }
            catch (DecoderFallbackException exception)
            {
                throw new ArgumentException("InvalidDefinitionTree: invalid UTF-8.", exception);
            }
            var metadata = text[..text.IndexOf('\t')].Split(' ', StringSplitOptions.None);
            var pathValue = text[(text.IndexOf('\t') + 1)..];
            if (metadata.Length != 3 || metadata.Any(string.IsNullOrEmpty)
                || metadata[1] is not ("blob" or "commit" or "tree")
                || !IsObjectId(metadata[2]) || !IsTreePath(pathValue))
                throw new ArgumentException($"InvalidDefinitionTree: {text}.");
            if (pathValue.StartsWith("Blueprint/", StringComparison.Ordinal)
                && pathValue.EndsWith(".scribe.cs", StringComparison.Ordinal)
                && !paths.Add(pathValue))
                throw new ArgumentException($"InvalidDefinitionTree: duplicate path {pathValue}.");
        }
        return paths;
    }

    private static bool IsObjectId(string value) =>
        value.Length is 40 or 64 && value.All(static character => character is >= '0' and <= '9' or >= 'a' and <= 'f');

    private static bool IsTreePath(string value) =>
        value.Length != 0 && !value.Contains('\\') && !Path.IsPathRooted(value)
        && !value.StartsWith("//", StringComparison.Ordinal)
        && !value.Split('/').Any(static segment => segment is "" or "." or "..")
        && !(value.Length >= 2 && value[1] == ':');

    private static int Verify(string directory, IReadOnlyDictionary<string, string> options,
        HashSet<string>? expectedDefinitionPaths, TextWriter output, TextWriter error)
    {
        var missing = Assets.Where(asset => !File.Exists(Path.Combine(directory, asset))).ToArray();
        if (missing.Length != 0)
        {
            foreach (var asset in missing) error.WriteLine($"MissingReleaseAsset: {asset}.");
            return 2;
        }
        var identity = ScribeReleaseIdentityCodec.Decode(File.ReadAllBytes(Path.Combine(directory, IdentityFile)));
        var pack = ScribeResourcePack.Open(Path.Combine(directory, ScribeResourceBundle.ResourceName));
        foreach (var entry in pack.Manifest.Entries) _ = pack.Read(entry.Gid);
        var bundle = ScribeResourceBundle.Open(Path.Combine(directory, ScribeResourceBundle.FileName));
        foreach (var entry in bundle.Manifest.Entries) _ = bundle.Read(entry.Gid);
        var mismatches = new List<string>();
        if (pack.Manifest.Version != identity.PackFormatVersion)
            mismatches.Add("PackFormatVersionMismatch: identity differs from zip manifest.");
        if (pack.Manifest.EntryCount != identity.EntryCount)
            mismatches.Add("EntryCountMismatch: identity differs from zip manifest.");
        if (pack.Manifest.TotalSha256 != identity.TotalSha256)
            mismatches.Add("TotalSha256Mismatch: identity differs from zip manifest.");
        if (bundle.Manifest.TotalSha256 != pack.Manifest.TotalSha256)
            mismatches.Add("BundleTotalSha256Mismatch: embedded pack differs from zip manifest.");
        if (options.TryGetValue("--source-commit", out var commit) && commit != identity.SourceCommit)
            mismatches.Add("SourceCommitMismatch: identity differs from expected source commit.");
        if (options.TryGetValue("--total-sha256", out var digest) && digest != identity.TotalSha256)
            mismatches.Add("ExpectedTotalSha256Mismatch: identity differs from expected digest.");
        if (expectedDefinitionPaths is not null)
        {
            var actualPaths = pack.Manifest.Entries.Select(entry => "Blueprint/" + entry.Gid + ".scribe.cs")
                .ToHashSet(StringComparer.Ordinal);
            foreach (var path in actualPaths.Except(expectedDefinitionPaths).Order(StringComparer.Ordinal))
                mismatches.Add($"UnexpectedDefinitionPath: {path}.");
            foreach (var path in expectedDefinitionPaths.Except(actualPaths).Order(StringComparer.Ordinal))
                mismatches.Add($"MissingDefinitionPath: {path}.");
        }
        foreach (var path in Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories).Order(StringComparer.Ordinal))
        {
            var relative = Path.GetRelativePath(directory, path);
            if (!Assets.Contains(relative, StringComparer.Ordinal))
                mismatches.Add($"UnexpectedReleaseEntry: {relative}.");
        }
        foreach (var mismatch in mismatches) error.WriteLine(mismatch);
        output.WriteLine(Summary("verify-release", identity));
        return mismatches.Count == 0 ? 0 : 1;
    }

    private static string Summary(string command, ScribeReleaseIdentity identity) => FormattableString.Invariant(
        $"resources {command}: sourceCommit={identity.SourceCommit} entries={identity.EntryCount} totalSha256={identity.TotalSha256}");
}
