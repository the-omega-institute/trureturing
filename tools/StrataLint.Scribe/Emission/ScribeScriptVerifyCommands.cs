using System.Collections.Immutable;
using System.Reflection;

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
            if (paths.IsEmpty)
            {
                error.WriteLine("EmptyScriptSelection: no definition paths were selected");
                return 1;
            }
            var current = DocumentDefinitions.Discover(documentsAssembly, repositoryRoot)
                .ToDictionary(item => item.Document.Header.Gid.Value, StringComparer.Ordinal);
            var results = ScribeScriptHost.ExecuteBatch(repositoryRoot, paths);
            var resultCounts = results.GroupBy(static result => result.RelativePath, StringComparer.Ordinal)
                .ToDictionary(static group => group.Key, static group => group.Count(), StringComparer.Ordinal);
            var resultFailures = paths.Where(path => resultCounts.GetValueOrDefault(path) != 1)
                .Select(path => $"{path}: ScriptResultCountMismatch expected=1 actual={resultCounts.GetValueOrDefault(path)}")
                .Concat(resultCounts.Keys.Except(paths, StringComparer.Ordinal)
                    .Select(static path => $"{path}: UnexpectedScriptResult"))
                .Order(StringComparer.Ordinal).ToArray();
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
            foreach (var resultFailure in resultFailures) error.WriteLine(resultFailure);
            foreach (var mismatch in mismatches.Order(StringComparer.Ordinal)) error.WriteLine(mismatch);
            output.WriteLine(FormattableString.Invariant($"scripts verify: paths={paths.Length} hostFailures={failures.Length + resultFailures.Length} mismatches={mismatches.Count}"));
            return failures.Length == 0 && resultFailures.Length == 0 && mismatches.Count == 0 ? 0 : 1;
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
