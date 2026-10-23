using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DagLedgerAlignWriter
{
    internal static CommandResult Align(string root, IRepositoryGateway repository, IReadOnlyList<string> arguments)
    {
        try
        {
            var options = ParseArguments(arguments);
            var source = new DagLedgerCommandPreparation.FileLeanReportSource(options.ReportPath);
            if (options.ListClosed)
            {
                var all = DagLedgerCommandPreparation.BuildTruth(repository, source);
                return new(true, JsonSerializer.Serialize(LeanTruthStates.Resolve(all.Snapshot, all.Lean)
                    .Where(static pair => pair.Value is TruthState.Closed).Select(static pair => pair.Key.Value)
                    .Order(StringComparer.Ordinal)) + "\n", string.Empty);
            }
            var selected = options.Selectors.Concat(options.Adds).Distinct().OrderBy(static path => path.Value, StringComparer.Ordinal).ToArray();
            var truth = selected.Length > 0
                ? DagLedgerCommandPreparation.BuildTruthScoped(repository, source, selected)
                : DagLedgerCommandPreparation.BuildTruth(repository, source);
            var states = LeanTruthStates.Resolve(truth.Snapshot, truth.Lean);
            var planned = new List<(RepoPath Path, FrozenStateRecord Record, bool Added)>();
            foreach (var path in selected)
            {
                var current = FrozenStateWriter.ReadCurrentBytes(root, path);
                if (options.Selectors.Contains(path) && current is null)
                    throw new InvalidOperationException($"selector {path.Value} is not a registered frozen-state member");
                if (current is { } bytes)
                    _ = FrozenStateRecordLoader.Load(new(FrozenStatePath.FromModulePath(path), bytes, Encoding.UTF8.GetString(bytes.AsSpan())));
                if (!truth.Snapshot.Files.ContainsKey(path)) throw new InvalidOperationException($"module {path.Value} does not exist");
                if (!states.TryGetValue(path, out var state) || state is not TruthState.Closed)
                    throw new InvalidOperationException($"module {path.Value} has TruthState={state}, expected Closed");
                if (!truth.Report.Files.TryGetValue(path, out var report))
                    throw new InvalidOperationException($"module {path.Value} has no current Lean report");
                planned.Add((path, FrozenStateRecord.FromReport(path, report), current is null));
            }
            if (!options.Retirements.IsEmpty)
            {
                foreach (var file in Directory.EnumerateFiles(Path.Combine(root, FrozenStatePath.Root), "*", SearchOption.AllDirectories))
                {
                    var statePath = Path.GetRelativePath(root, file).Replace('\\', '/');
                    if (!FrozenStatePath.TryToModulePath(statePath, out var module)) throw new FormatException("invalid frozen state path: " + statePath);
                    if (!truth.Snapshot.Files.ContainsKey(module) && !options.Retirements.Contains(module))
                        throw new InvalidOperationException($"module {module.Value} does not exist; missing registrations require explicit --retire-registration");
                }
            }
            foreach (var retired in options.Retirements)
            {
                if (!retired.Value.StartsWith("D5/", StringComparison.Ordinal))
                    throw new InvalidOperationException($"registration retirement requires a D5 module: {retired.Value}");
                if (truth.Snapshot.Files.ContainsKey(retired)) throw new InvalidOperationException($"cannot retire existing module {retired.Value}");
                var pin = FrozenStateWriter.ReadCurrentBytes(root, retired)
                    ?? throw new InvalidOperationException($"selector {retired.Value} is not a registered frozen-state member");
                _ = FrozenStateRecordLoader.Load(new(FrozenStatePath.FromModulePath(retired), pin, Encoding.UTF8.GetString(pin.AsSpan())));
                foreach (var (path, report) in truth.Report.Files)
                    if (report.Imports.Contains(LeanImportClosure.ModuleName(retired)))
                        throw new InvalidOperationException($"module {path.Value} still imports retired registration {retired.Value}");
                foreach (var file in truth.Snapshot.Files.Values.Where(static file => LeanClosureValidator.IsReportLean(file.Path.Value)))
                    if (LeanSourceCatalog.ParseFileImports(file).Contains(LeanImportClosure.ModuleName(retired)))
                        throw new InvalidOperationException($"module {file.Path.Value} still imports retired registration {retired.Value}");
            }
            var backups = planned.Select(static item => item.Path).Concat(options.Retirements)
                .ToDictionary(static path => path, path => FrozenStateWriter.ReadCurrentBytes(root, path));
            var changed = 0;
            var added = 0;
            try
            {
                foreach (var item in planned)
                    if (FrozenStateWriter.Write(root, item.Path, item.Record.StatementId, item.Record.Declarations))
                    {
                        if (item.Added) added++; else changed++;
                    }
                foreach (var path in options.Retirements) _ = FrozenStateWriter.Delete(root, path);
            }
            catch
            {
                foreach (var (path, bytes) in backups) FrozenStateWriter.Restore(root, path, bytes);
                throw;
            }
            return new(true, Summary(selected.Length, changed, added, selected.Length - changed - added)
                + (options.Retirements.IsEmpty ? string.Empty : $"LEDGER_RETIRE registrations={options.Retirements.Length}\n"), string.Empty);
        }
        catch (Exception exception) when (exception is ArgumentException or FormatException or IOException
            or InvalidOperationException or JsonException or UnauthorizedAccessException
            or DagLedgerCommandPreparation.LeanReportUnusableException or DagLedgerCommandPreparation.RepositoryUnavailableException)
        {
            return new(false, Summary(0, 0, 0, 0, 1), "LEDGER_ALIGN_FAILED " + exception.Message
                + (exception.InnerException is null ? string.Empty : " Cause: " + exception.InnerException.Message) + "\n");
        }
    }

    private static AlignOptions ParseArguments(IReadOnlyList<string> arguments)
    {
        string? report = null;
        var selectors = ImmutableArray.CreateBuilder<RepoPath>();
        var adds = ImmutableArray.CreateBuilder<RepoPath>();
        var retirements = ImmutableArray.CreateBuilder<RepoPath>();
        var list = false;
        for (var index = 0; index < arguments.Count; index++)
            switch (arguments[index])
            {
                case "--candidate-lean-report" when ++index < arguments.Count && report is null: report = arguments[index]; break;
                case "--selector" when ++index < arguments.Count: selectors.Add(Module(arguments[index])); break;
                case "--add" when ++index < arguments.Count: adds.Add(Module(arguments[index])); break;
                case "--retire-registration" when ++index < arguments.Count: retirements.Add(Module(arguments[index])); break;
                case "--list-closed" when !list: list = true; break;
                default: throw Usage();
            }
        var selectionCount = selectors.Count + adds.Count + retirements.Count;
        if (string.IsNullOrWhiteSpace(report) || (list ? selectionCount != 0 : selectionCount == 0)) throw Usage();
        if (selectors.Concat(adds).Concat(retirements).GroupBy(static path => path).Any(static group => group.Count() != 1))
            throw new InvalidOperationException("duplicate or conflicting module selector");
        return new(report, selectors.ToImmutable(), adds.ToImmutable(), retirements.ToImmutable(), list);
    }

    private static RepoPath Module(string value)
    {
        if (!RepoPath.TryCreate(value, out var path)) throw new FormatException("module selector is not canonical: " + value);
        _ = FrozenStatePath.FromModulePath(path);
        return path;
    }
    private static InvalidOperationException Usage() => new("USAGE: StrataLint ledger-align --candidate-lean-report FILE "
        + "(--list-closed | (--selector MODULE | --add MODULE | --retire-registration MODULE)...)");
    private static string Summary(int considered, int changed, int added, int unchanged, int conflicts = 0) =>
        $"LEDGER_ALIGN selectors_considered={considered} changed={changed} added={added} unchanged={unchanged} conflicts={conflicts}\n";
    private sealed record AlignOptions(string ReportPath, ImmutableArray<RepoPath> Selectors,
        ImmutableArray<RepoPath> Adds, ImmutableArray<RepoPath> Retirements, bool ListClosed);
}
