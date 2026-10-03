using System.Collections.Immutable;

namespace StrataLint.Scribe;

internal static class ScribeRelationVerifyCommands
{
    internal static int Run(IReadOnlyList<string> arguments, string root,
        TextReader? input, TextWriter output, TextWriter error)
    {
        if (arguments.Count is not (2 or 4) || arguments[1] != "verify"
            || arguments.Count == 4 && (arguments[2] != "--paths-from" || string.IsNullOrWhiteSpace(arguments[3])))
        {
            error.WriteLine("usage: relations verify [--paths-from <file|->]");
            return 2;
        }
        try
        {
            var paths = arguments.Count == 4
                ? ReadPaths(arguments[3], input)
                : Directory.EnumerateFiles(Path.Combine(root, "Blueprint"), "*.scribe.cs", SearchOption.AllDirectories)
                    .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/')).Order(StringComparer.Ordinal).ToImmutableArray();
            if (paths.IsEmpty || paths.Any(path => ScribeScriptHost.NormalizePath(path) is null
                || !File.Exists(Path.Combine(root, path))))
            {
                error.WriteLine("InvalidRelationSelection: select existing Blueprint definition paths");
                return 2;
            }
            return RelationVerifier.Verify(root, paths).Write(output, error);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException or ArgumentException)
        {
            error.WriteLine(exception.Message);
            return 2;
        }
    }

    private static ImmutableArray<string> ReadPaths(string path, TextReader? input) =>
        (path == "-" ? (input ?? Console.In).ReadToEnd() : File.ReadAllText(path))
            .Split(['\0', '\r', '\n'], StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries)
            .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray();
}
