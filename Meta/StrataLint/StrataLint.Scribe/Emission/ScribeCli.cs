namespace StrataLint.Scribe;

public static class ScribeCli
{
    public static int Run(
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TextWriter output,
        TextWriter error)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentException.ThrowIfNullOrWhiteSpace(workingDirectory);
        ArgumentNullException.ThrowIfNull(output);
        ArgumentNullException.ThrowIfNull(error);

        var check = arguments.Count == 2
            && string.Equals(arguments[1], "--check", StringComparison.Ordinal);
        if (arguments.Count is < 1 or > 2
            || !string.Equals(arguments[0], "emit", StringComparison.Ordinal)
            || (arguments.Count == 2 && !check))
        {
            error.WriteLine("usage: dotnet run --project Meta/StrataLint/StrataLint.Scribe -- emit [--check]");
            return 2;
        }

        try
        {
            var repositoryRoot = FindRepositoryRoot(workingDirectory);
            return ScribeEmitter.Emit(repositoryRoot, check, output, error);
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
