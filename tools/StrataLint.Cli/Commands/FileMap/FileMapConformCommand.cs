using System.Text;
using StrataLint.EngineeringScope;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal static class FileMapConformCommand
{
    internal const string Usage =
        "USAGE: StrataLint filemap-conform [--producer-write-set PRODUCER | --scope PATH]";

    internal static ExplicitCommandResult Run(
        IReadOnlyList<string> arguments,
        string repositoryRoot)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var writeSetQuery = arguments.Count == 2
            && arguments[0] == "--producer-write-set"
            && !string.IsNullOrWhiteSpace(arguments[1]);
        var scoped = arguments.Count == 2 && arguments[0] == "--scope" && !string.IsNullOrWhiteSpace(arguments[1]);
        if (arguments.Count != 0 && !writeSetQuery && !scoped)
        {
            return new ExplicitCommandResult(2, string.Empty, Usage + "\n");
        }

        try
        {
            if (writeSetQuery)
            {
                var patterns = FileMapLoader.LoadRepository(repositoryRoot).Entries
                    .Where(entry => string.Equals(
                        entry.ProducedBy,
                        arguments[1],
                        StringComparison.Ordinal))
                    .Where(static entry => entry.RuntimeDisposition.StartsWith(
                        "committed-",
                        StringComparison.Ordinal))
                    .Select(static entry => entry.Pattern)
                    .Order(StringComparer.Ordinal)
                    .ToArray();
                return patterns.Length == 0
                    ? new ExplicitCommandResult(
                        2,
                        string.Empty,
                        $"INFRASTRUCTURE_FAILURE filemap-conform: producer {arguments[1]} has no committed write set\n")
                    : new ExplicitCommandResult(
                        0,
                        string.Concat(patterns.Select(static pattern => pattern + "\n")),
                        string.Empty);
            }

            var scope = scoped ? FileMapInspectionScope.Read(Path.GetFullPath(arguments[1], repositoryRoot)) : null;
            var result = Render(FileMapPolicy.InspectRepository(repositoryRoot, scope));
            return scope is null ? result : result with { Output = DescribeScope(scope) + result.Output };
        }
        catch (Exception exception)
        {
            return new ExplicitCommandResult(
                2,
                string.Empty,
                $"INFRASTRUCTURE_FAILURE filemap-conform: {exception.Message}\n");
        }
    }

    internal static string DescribeScope(FileMapInspectionScope scope) => "FILEMAP_SCOPE "
        + System.Text.Json.JsonSerializer.Serialize(new { scope = scope.Paths is null ? "whole-tree" : "delta",
            paths = scope.Paths?.Length, actors = scope.Actors, inventory = scope.Paths is null || scope.Inventory }) + "\n";

    internal static ExplicitCommandResult Render(IReadOnlyList<FileMapFinding> findings)
    {
        ArgumentNullException.ThrowIfNull(findings);
        if (findings.Count == 0)
        {
            return new ExplicitCommandResult(0, string.Empty, string.Empty);
        }

        var output = new StringBuilder();
        foreach (var finding in findings
            .OrderBy(static item => item.Path, StringComparer.Ordinal)
            .ThenBy(static item => item.Code, StringComparer.Ordinal))
        {
            output.Append(finding.Code);
            output.Append(' ');
            output.Append(finding.Path);
            output.Append(": ");
            output.Append(finding.Message);
            output.Append('\n');
        }

        return new ExplicitCommandResult(1, output.ToString(), string.Empty);
    }
}
