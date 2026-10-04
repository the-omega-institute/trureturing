using System.Collections.Immutable;

namespace StrataLint.Scribe;

internal static class ScribeScriptVerifyCommands
{
    internal static int Run(IReadOnlyList<string> arguments,
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
            var selection = ScribeDefinitionSelector.Select(repositoryRoot, paths);
            if (!selection.IsSuccess)
            {
                error.WriteLine(selection.Failure);
                return 2;
            }
            var admission = ScribeSdkAdmission.Check(repositoryRoot, selection.Paths, paths);
            if (admission.ExitCode != 0)
            {
                admission.WriteFailure(error);
                return admission.ExitCode;
            }
            paths = selection.Paths;
            var results = ScribeScriptHost.ExecuteBatch(repositoryRoot, paths);
            var resultCounts = results.GroupBy(static result => result.RelativePath, StringComparer.Ordinal)
                .ToDictionary(static group => group.Key, static group => group.Count(), StringComparer.Ordinal);
            var resultFailures = paths.Where(path => resultCounts.GetValueOrDefault(path) != 1)
                .Select(path => $"{path}: ScriptResultCountMismatch expected=1 actual={resultCounts.GetValueOrDefault(path)}")
                .Concat(resultCounts.Keys.Except(paths, StringComparer.Ordinal)
                    .Select(static path => $"{path}: UnexpectedScriptResult"))
                .Order(StringComparer.Ordinal).ToArray();
            var failures = results.Where(result => !result.IsSuccess).ToArray();
            foreach (var failure in failures) error.WriteLine(failure.Failure);
            foreach (var resultFailure in resultFailures) error.WriteLine(resultFailure);
            output.WriteLine(FormattableString.Invariant($"scripts verify: paths={paths.Length} hostFailures={failures.Length + resultFailures.Length}"));
            return failures.Length == 0 && resultFailures.Length == 0 ? 0 : 1;
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
