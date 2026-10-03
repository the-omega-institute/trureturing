using StrataLint.Engine;

namespace StrataLint.Scribe;

internal static class ScribeResourceCompareCommand
{
    internal static int Run(IReadOnlyList<string> arguments, string workingDirectory,
        Func<string> repositoryRoot, TextWriter output, TextWriter error)
    {
        if (arguments.Count != 4 || arguments[2] != "--pack" || string.IsNullOrWhiteSpace(arguments[3]))
        {
            error.WriteLine(ScribeResourceCommands.Usage);
            return 2;
        }
        try
        {
            var pack = ScribeResourcePack.Open(Path.GetFullPath(arguments[3], workingDirectory));
            var root = repositoryRoot();
            var current = Directory.EnumerateFiles(Path.Combine(root, "Blueprint"), "*.scribe.cs", SearchOption.AllDirectories)
                .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/')).ToHashSet(StringComparer.Ordinal);
            var consistent = 0;
            var changed = 0;
            var packOnly = 0;
            foreach (var entry in pack.Manifest.Entries)
            {
                var definitionPath = ScribeEmissionAttestation.DefinitionPath(entry.Gid);
                var entryInput = entry.Inputs.SingleOrDefault(input => input.Path == definitionPath && input.Sha256 is not null)
                    ?? throw new ScribeResourcePackException(ScribeResourcePackErrorCode.InvalidManifest,
                        $"Definition input is missing: {definitionPath}.");
                if (!current.Remove(definitionPath))
                {
                    packOnly++;
                    error.WriteLine($"{definitionPath}: input={definitionPath} recorded={entryInput.Sha256} current=missing (packOnly)");
                    continue;
                }
                ScribeResourceInput? difference = null;
                string? actual = null;
                foreach (var input in entry.Inputs)
                {
                    var path = Path.Combine(root, input.Path.Replace('/', Path.DirectorySeparatorChar));
                    var digest = File.Exists(path) ? ScribeResourcePack.Digest(File.ReadAllBytes(path)) : null;
                    if (input.Sha256 == digest) continue;
                    difference = input;
                    actual = digest;
                    break;
                }
                if (difference is null) consistent++;
                else
                {
                    changed++;
                    error.WriteLine($"{definitionPath}: input={difference.Path} recorded={difference.Sha256 ?? "missing"} current={actual ?? "missing"}");
                }
            }
            foreach (var path in current.Order(StringComparer.Ordinal))
            {
                var digest = ScribeResourcePack.Digest(File.ReadAllBytes(Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar))));
                error.WriteLine($"{path}: input={path} recorded=missing current={digest} (diskOnly)");
            }
            output.WriteLine(FormattableString.Invariant(
                $"resources compare: entries={pack.Manifest.EntryCount} consistent={consistent} inputsChanged={changed} packOnly={packOnly} diskOnly={current.Count}"));
            return changed + packOnly + current.Count == 0 ? 0 : 1;
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or ArgumentException or FormatException or InvalidOperationException)
        {
            error.WriteLine(exception.Message);
            return 2;
        }
    }
}
