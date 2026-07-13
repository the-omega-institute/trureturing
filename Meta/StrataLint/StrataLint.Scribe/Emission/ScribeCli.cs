using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class ScribeCli
{
    public static int Run(
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TextWriter output,
        TextWriter error) =>
        Run(arguments, workingDirectory, output, error, leanReport: null);

    internal static int Run(
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TextWriter output,
        TextWriter error,
        LeanAxiomReport? leanReport)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentException.ThrowIfNullOrWhiteSpace(workingDirectory);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);

        var check = arguments.Count == 2
            && string.Equals(arguments[1], "--check", StringComparison.Ordinal);
        var command = arguments.Count == 0 ? string.Empty : arguments[0];
        if (arguments.Count is < 1 or > 2
            || command is not ("emit" or "catalog")
            || (arguments.Count == 2 && !check))
        {
            error.WriteLine(
                "usage: dotnet run --project Meta/StrataLint/StrataLint.Scribe -- emit|catalog [--check]");
            return 2;
        }

        try
        {
            var repositoryRoot = FindRepositoryRoot(workingDirectory);
            if (command == "catalog")
            {
                return AnchorCatalogEmitter.Emit(repositoryRoot, check, output, error);
            }

            return leanReport is null
                ? ScribeEmitter.Emit(repositoryRoot, check, output, error)
                : ScribeEmitter.Emit(repositoryRoot, check, output, error, leanReport);
        }
        catch (Exception exception) when (
            exception is IOException or UnauthorizedAccessException or ArgumentException)
        {
            error.WriteLine(exception.Message);
            return 2;
        }
    }

    private static string FindRepositoryRoot(string workingDirectory)
    {
        for (var current = new DirectoryInfo(Path.GetFullPath(workingDirectory));
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "global.json"))
                && Directory.Exists(Path.Combine(current.FullName, "Blueprint")))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException(
            "Could not locate a repository root containing global.json and Blueprint/.");
    }
}
