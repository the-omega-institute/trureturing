using System.Collections.Immutable;
using System.Reflection;
using StrataLint.Scribe.Scripting;

namespace StrataLint.Scribe;

internal static class ScribeScriptVerifyCommands
{
    internal static int Run(Assembly documentsAssembly, IReadOnlyList<string> arguments,
        string repositoryRoot, TextReader? input, TextWriter output, TextWriter error)
    {
        if (arguments.Count is not (2 or 4) || arguments[0] != "scripts" || arguments[1] != "verify"
            || (arguments.Count == 4 && (arguments[2] != "--paths-from" || string.IsNullOrWhiteSpace(arguments[3]))))
        {
            error.WriteLine(Usage);
            return 2;
        }
        try
        {
            var paths = arguments.Count == 4 ? ReadPaths(arguments[3], input)
                : Directory.EnumerateFiles(Path.Combine(repositoryRoot, "Blueprint"), "*.scribe.cs", SearchOption.AllDirectories)
                    .Select(path => Path.GetRelativePath(repositoryRoot, path).Replace('\\', '/'))
                    .Order(StringComparer.Ordinal).ToImmutableArray();
            var current = DocumentDefinitions.Discover(documentsAssembly, repositoryRoot)
                .ToDictionary(item => item.Document.Header.Gid.Value, StringComparer.Ordinal);
            var results = ScribeScriptHost.ExecuteBatch(repositoryRoot, paths);
            var failures = results.Where(result => !result.IsSuccess).ToArray();
            var mismatches = new List<string>();
            foreach (var result in results.Where(static result => result.IsSuccess))
            {
                var gid = result.Definition!.Document.Header.Gid.Value;
                if (!current.TryGetValue(gid, out var existing))
                {
                    mismatches.Add($"{result.RelativePath}: MissingAssemblyDefinition");
                    continue;
                }
                if (!ScribeResourceCodec.Encode(result.Definition).AsSpan()
                    .SequenceEqual(ScribeResourceCodec.Encode(existing)))
                    mismatches.Add($"{result.RelativePath}: CanonicalContentMismatch");
            }
            foreach (var failure in failures) error.WriteLine(failure.Failure);
            foreach (var mismatch in mismatches.Order(StringComparer.Ordinal)) error.WriteLine(mismatch);
            output.WriteLine(FormattableString.Invariant($"scripts verify: paths={paths.Length} hostFailures={failures.Length} mismatches={mismatches.Count}"));
            return failures.Length == 0 && mismatches.Count == 0 ? 0 : 1;
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or ArgumentException or FormatException or InvalidOperationException)
        {
            error.WriteLine(exception.Message);
            return 2;
        }
    }

    private const string Usage = "usage: scripts verify [--paths-from <file|->]";

    private static ImmutableArray<string> ReadPaths(string path, TextReader? input)
    {
        var payload = path == "-" ? (input ?? Console.In).ReadToEnd() : File.ReadAllText(path);
        return payload.Split(['\0', '\r', '\n'], StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries)
            .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray();
    }
}
