namespace StrataLint.Scribe;

internal static class ScribeReleaseCommands
{
    private static readonly string[] Assets = [ScribeResourceBundle.ResourceName, ScribeResourceBundle.FileName];

    internal static int Run(IReadOnlyList<string> arguments, string workingDirectory,
        Func<string> repositoryRoot, TextWriter output, TextWriter error)
    {
        try
        {
            var release = arguments[1] == "release";
            var options = Parse(arguments, release);
            var directory = Path.GetFullPath(options[release ? "--out" : "--dir"], workingDirectory);
            return release
                ? Release(repositoryRoot(), directory, output, error)
                : Verify(directory, options, output, error);
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
        var allowed = release ? new[] { "--out" } : ["--dir", "--total-sha256"];
        if (arguments.Count < 4 || arguments.Count % 2 != 0)
            throw new ArgumentException("InvalidReleaseArguments: options require a name and value.");
        for (var index = 2; index < arguments.Count; index += 2)
        {
            if (!allowed.Contains(arguments[index], StringComparer.Ordinal)
                || string.IsNullOrWhiteSpace(arguments[index + 1])
                || !options.TryAdd(arguments[index], arguments[index + 1]))
                throw new ArgumentException("InvalidReleaseArguments: unknown, empty or duplicate option.");
        }
        if (!options.ContainsKey(release ? "--out" : "--dir"))
            throw new ArgumentException("InvalidReleaseArguments: required option is missing.");
        if (options.TryGetValue("--total-sha256", out var digest)
            && (digest.Length != 64 || !digest.All(static character => character is >= '0' and <= '9' or >= 'a' and <= 'f')))
            throw new ArgumentException("InvalidTotalSha256: requires 64 lowercase hexadecimal characters.");
        return options;
    }

    private static int Release(string root, string directory, TextWriter output, TextWriter error)
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
            File.WriteAllBytes(Path.Combine(staging.FullName, ScribeResourceBundle.FileName),
                ScribeResourceBundle.Write(File.ReadAllBytes(packPath)));
            Publish(staging.FullName, directory);
            output.WriteLine(Summary("release", manifest));
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

    private static int Verify(string directory, IReadOnlyDictionary<string, string> options,
        TextWriter output, TextWriter error)
    {
        var missing = Assets.Where(asset => !File.Exists(Path.Combine(directory, asset))).ToArray();
        if (missing.Length != 0)
        {
            foreach (var asset in missing) error.WriteLine($"MissingReleaseAsset: {asset}.");
            return 2;
        }
        var packBytes = File.ReadAllBytes(Path.Combine(directory, ScribeResourceBundle.ResourceName));
        var pack = ScribeResourcePack.Open(packBytes);
        foreach (var entry in pack.Manifest.Entries) _ = pack.Read(entry.Gid);
        var embeddedPackBytes = ScribeResourceBundle.ReadPackBytes(
            File.ReadAllBytes(Path.Combine(directory, ScribeResourceBundle.FileName)));
        var bundle = ScribeResourcePack.Open(embeddedPackBytes);
        foreach (var entry in bundle.Manifest.Entries) _ = bundle.Read(entry.Gid);
        var mismatches = new List<string>();
        if (!embeddedPackBytes.AsSpan().SequenceEqual(packBytes))
            mismatches.Add("BundlePackBytesMismatch: embedded pack differs from zip bytes.");
        if (options.TryGetValue("--total-sha256", out var digest) && digest != pack.Manifest.TotalSha256)
            mismatches.Add("ExpectedTotalSha256Mismatch: zip manifest differs from expected digest.");
        foreach (var path in Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories).Order(StringComparer.Ordinal))
        {
            var relative = Path.GetRelativePath(directory, path);
            if (!Assets.Contains(relative, StringComparer.Ordinal))
                mismatches.Add($"UnexpectedReleaseEntry: {relative}.");
        }
        foreach (var mismatch in mismatches) error.WriteLine(mismatch);
        output.WriteLine(Summary("verify-release", pack.Manifest));
        return mismatches.Count == 0 ? 0 : 1;
    }

    private static string Summary(string command, ScribeResourcePackManifest manifest) => FormattableString.Invariant(
        $"resources {command}: entries={manifest.EntryCount} totalSha256={manifest.TotalSha256}");
}
