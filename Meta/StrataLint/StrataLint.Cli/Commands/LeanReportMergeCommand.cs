using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class LeanReportMergeCommand
{
    internal static CommandResult Run(IReadOnlyList<string> arguments)
    {
        var options = Parse(arguments);
        var decoded = SnapshotDecoder.Decode(GitRepositorySnapshotReader.ReadCurrent(options.Repository));
        var snapshot = decoded is SnapshotDecodeOutcome.Decoded success
            ? success.Snapshot
            : throw new FormatException(((SnapshotDecodeOutcome.InfrastructureFailure)decoded).Message);
        var cached = RawLeanReportArtifact.ReadPartialFile(options.Cached, snapshot);
        var fresh = RawLeanReportArtifact.ReadPartialFile(options.Fresh, snapshot);
        var selectedPaths = File.ReadAllLines(options.CachedModulesFile)
            .Where(static line => !string.IsNullOrWhiteSpace(line))
            .Select(ModulePath)
            .ToHashSet(StringComparer.Ordinal);
        var merged = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal);
        foreach (var (path, report) in cached.Files)
        {
            if (selectedPaths.Contains(path.Value)) merged.Add(path.Value, report);
        }

        if (merged.Count != selectedPaths.Count)
        {
            throw new FormatException("Cached Lean report does not contain every selected module.");
        }

        foreach (var (path, report) in fresh.Files)
        {
            if (!merged.TryAdd(path.Value, report))
            {
                throw new FormatException($"Lean report contains duplicate path {path.Value}.");
            }
        }

        var bytes = RawLeanReportArtifact.Write(snapshot, LeanAxiomReport.Create(merged));
        File.WriteAllBytes(options.Output, bytes.AsSpan().ToArray());
        return new CommandResult(true, string.Empty, string.Empty);
    }

    private static string ModulePath(string module)
    {
        if (module == "Trureturing") return "Trureturing.lean";
        if (!module.StartsWith("D5.", StringComparison.Ordinal))
        {
            throw new FormatException($"Selected Lean module is not managed: {module}.");
        }

        return module.Replace('.', '/') + ".lean";
    }

    private static Options Parse(IReadOnlyList<string> arguments)
    {
        string? repository = null;
        string? cached = null;
        string? fresh = null;
        string? output = null;
        string? modules = null;
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count) throw new ArgumentException("lean-report-merge options require values.");
            switch (arguments[index])
            {
                case "--repository": repository = arguments[index + 1]; break;
                case "--cached": cached = arguments[index + 1]; break;
                case "--fresh": fresh = arguments[index + 1]; break;
                case "--output": output = arguments[index + 1]; break;
                case "--cached-modules-file": modules = arguments[index + 1]; break;
                default: throw new ArgumentException($"lean-report-merge: unknown argument '{arguments[index]}'.");
            }
        }

        return new Options(
            Require(repository, "--repository"), Require(cached, "--cached"),
            Require(fresh, "--fresh"), Require(output, "--output"),
            Require(modules, "--cached-modules-file"));
    }

    private static string Require(string? value, string option) =>
        string.IsNullOrWhiteSpace(value) ? throw new ArgumentException($"lean-report-merge requires {option}.") : value;

    private sealed record Options(string Repository, string Cached, string Fresh, string Output, string CachedModulesFile);
}
