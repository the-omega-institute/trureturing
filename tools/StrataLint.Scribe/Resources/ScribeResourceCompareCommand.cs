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
            var result = ScribeResourceCorrespondence.Compare(pack, repositoryRoot());
            var differences = result.InputsChanged.Select(difference => (Difference: difference, Suffix: ""))
                .Concat(result.PackOnly.Select(difference => (Difference: difference, Suffix: " (packOnly)")))
                .OrderBy(item => item.Difference.DefinitionPath, StringComparer.Ordinal);
            foreach (var (difference, suffix) in differences) error.WriteLine(difference + suffix);
            foreach (var difference in result.DiskOnly) error.WriteLine(difference + " (diskOnly)");
            output.WriteLine(FormattableString.Invariant(
                $"resources compare: entries={pack.Manifest.EntryCount} consistent={result.ConsistentCount} inputsChanged={result.InputsChanged.Length} packOnly={result.PackOnly.Length} diskOnly={result.DiskOnly.Length}"));
            return result.IsCorresponding ? 0 : 1;
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or ArgumentException or FormatException or InvalidOperationException)
        {
            error.WriteLine(exception.Message);
            return 2;
        }
    }
}
