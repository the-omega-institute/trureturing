using System.Collections.Immutable;
using StrataLint.Scribe;

namespace StrataLint.Cli;

internal static class RunHandleCommand
{
    internal static ExplicitCommandResult Produce(string repositoryRoot, IReadOnlyList<string> arguments)
    {
        if (!TryPair(arguments, "--request", "--output-root", out var request, out var outputRoot)) return Usage("run-produce --request FILE --output-root DIR");
        var result = RunHandleProducer.Produce(repositoryRoot, outputRoot, File.ReadAllBytes(request), Inventory(repositoryRoot));
        return new(result.ExitCode, result.ExitCode == 0 ? result.Diagnostic : string.Empty, result.ExitCode == 0 ? string.Empty : result.Diagnostic);
    }

    internal static ExplicitCommandResult Consume(string repositoryRoot, IReadOnlyList<string> arguments)
    {
        if (!TryPair(arguments, "--output-root", "--expected-request-sha256", out var outputRoot, out var expected)) return Usage("run-consume --output-root DIR --expected-request-sha256 SHA256");
        var result = RunHandleConsumer.Consume(outputRoot, expected, Inventory(repositoryRoot));
        return new(result.ExitCode, result.ExitCode == 0 ? result.Diagnostic : string.Empty, result.ExitCode == 0 ? string.Empty : result.Diagnostic);
    }

    internal static ImmutableArray<RunArtifactInventoryItem> Inventory(string repositoryRoot) =>
        FileMapLoader.LoadRepository(repositoryRoot).Entries
            .Where(static entry => entry.Kind is FileMapKind.Generated && entry.ArtifactId != "none")
            .Select(static entry => new RunArtifactInventoryItem(entry.ArtifactId, entry.Pattern, entry.Mode!))
            .OrderBy(static entry => entry.Path, StringComparer.Ordinal)
            .ThenBy(static entry => entry.ArtifactId, StringComparer.Ordinal)
            .ToImmutableArray();

    private static bool TryPair(IReadOnlyList<string> args, string firstName, string secondName, out string first, out string second)
    {
        first = second = string.Empty;
        if (args.Count != 4) return false;
        for (var index = 0; index < args.Count; index += 2)
        {
            if (args[index] == firstName && first.Length == 0) first = args[index + 1];
            else if (args[index] == secondName && second.Length == 0) second = args[index + 1];
            else return false;
        }
        return first.Length != 0 && second.Length != 0;
    }

    private static ExplicitCommandResult Usage(string usage) => new(2, string.Empty, "USAGE: StrataLint " + usage + "\n");
}
