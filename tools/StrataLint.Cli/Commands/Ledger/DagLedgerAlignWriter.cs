using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DagLedgerAlignWriter
{
    private const string AliasNotice =
        "ledger-append is an alias of ledger-align --add <module> "
        + "(expand phase; removed at contract)\n";

    internal static CommandResult Align(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments) =>
        Execute(repositoryRoot, repository, arguments, appendAlias: false);

    internal static CommandResult AppendAlias(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments) =>
        Execute(repositoryRoot, repository, arguments, appendAlias: true);

    private static CommandResult Execute(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments,
        bool appendAlias)
    {
        var prefix = appendAlias ? AliasNotice : string.Empty;
        try
        {
            var options = ParseArguments(arguments, appendAlias);
            var result = options.FromAccepted
                ? MaterializeAccepted(repositoryRoot)
                : AlignFromReport(repositoryRoot, repository, options, appendAlias);
            return result with { Output = prefix + result.Output };
        }
        catch (Exception exception) when (
            exception is ArgumentException
                or FormatException
                or IOException
                or InvalidOperationException
                or JsonException
                or KeyNotFoundException
                or UnauthorizedAccessException
                or DagLedgerCommandPreparation.LeanReportUnusableException
                or DagLedgerCommandPreparation.RepositoryUnavailableException)
        {
            return new CommandResult(
                false,
                prefix + RenderSummary(0, 0, 0, 0, 1),
                DagLedgerAppendWriter.RenderFailure("LEDGER_ALIGN_FAILED", exception));
        }
    }

    private static CommandResult MaterializeAccepted(string repositoryRoot)
    {
        var ledgerPath = LedgerPath(repositoryRoot);
        var acceptedFiles = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(ledgerPath);
        var events = LoadOrderedEvents(acceptedFiles, "accepted frozen ledger");
        var baseView = ReadView(acceptedFiles);
        var state = ReadStateCatalog(repositoryRoot);
        var active = baseView.ActiveByPath.Values
            .OrderBy(static entry => entry.Material.RepoPath.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        var conflicts = active
            .Where(entry => state.Records.TryGetValue(entry.Material.RepoPath, out var record)
                && record.StatementId != entry.Material.StatementId)
            .ToImmutableArray();
        var stateBefore = state.Records.Count;
        if (!conflicts.IsEmpty)
        {
            var output = RenderAcceptedCounts(
                    active.Length,
                    stateBefore,
                    stateBefore,
                    written: 0,
                    conflicts.Length)
                + RenderSummary(
                    active.Length,
                    changed: 0,
                    added: 0,
                    unchanged: active.Count(entry =>
                        state.Records.TryGetValue(entry.Material.RepoPath, out var record)
                        && record.StatementId == entry.Material.StatementId),
                    conflicts.Length);
            var names = string.Join(
                ", ",
                conflicts.Select(static entry => entry.Material.RepoPath.Value));
            return new CommandResult(
                false,
                output,
                $"LEDGER_ALIGN_FAILED state/event statement_id conflicts: {names}\n");
        }

        var eventsByPath = events.ToImmutableDictionary(static item => item.DescriptorPath);
        var missing = active
            .Where(entry => !state.Records.ContainsKey(entry.Material.RepoPath))
            .Select(entry => eventsByPath[entry.Material.RepoPath])
            .ToImmutableArray();
        if (!missing.IsEmpty)
        {
            FrozenLedgerPublication.PublishSnapshot(
                repositoryRoot,
                ledgerPath,
                acceptedFiles,
                acceptedFiles,
                missing,
                [],
                "ledger-align --from-accepted");
        }

        return new CommandResult(
            true,
            RenderAcceptedCounts(
                active.Length,
                stateBefore,
                stateBefore + missing.Length,
                missing.Length,
                conflicts: 0)
            + RenderSummary(
                active.Length,
                changed: 0,
                added: missing.Length,
                unchanged: active.Length - missing.Length,
                conflicts: 0),
            string.Empty);
    }

    private static CommandResult AlignFromReport(
        string repositoryRoot,
        IRepositoryGateway repository,
        AlignOptions options,
        bool appendAlias)
    {
        var truth = DagLedgerCommandPreparation.BuildTruth(
            repository,
            new DagLedgerCommandPreparation.FileLeanReportSource(options.ReportPath!));
        var states = LeanTruthStates.Resolve(truth.Snapshot, truth.Lean);
        ValidateRequestedPaths(options, truth.Snapshot, states);

        var adjacency = LeanImportAdjacency.Build(truth.Snapshot, truth.Lean);
        var catalog = FrozenContentAddress.Build(
            truth.Snapshot,
            truth.Lean,
            states,
            adjacency) switch
        {
            FrozenMaterialOutcome.Accepted accepted => accepted.Capability,
            FrozenMaterialOutcome.Rejected rejected => throw new InvalidOperationException(
                "complete frozen catalog build failed: " + rejected.Message),
            _ => throw new InvalidOperationException("unknown frozen material outcome"),
        };
        var ledgerPath = LedgerPath(repositoryRoot);
        var acceptedFiles = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(ledgerPath);
        _ = LoadOrderedEvents(acceptedFiles, "accepted frozen ledger");
        var baseView = ReadView(acceptedFiles);
        var state = ReadStateCatalog(repositoryRoot);

        var addPaths = appendAlias
            ? catalog.ClosedNodes
                .Where(node => !baseView.ActiveByPath.ContainsKey(node.RepoPath))
                .Select(static node => node.RepoPath)
                .ToImmutableArray()
            : options.Adds;
        var selected = options.Selectors.IsEmpty
            ? state.Records.Keys.ToImmutableArray()
            : options.Selectors;
        foreach (var selector in options.Selectors)
        {
            if (!state.Records.ContainsKey(selector))
            {
                throw new InvalidOperationException(
                    $"selector {selector.Value} is not a registered frozen-state member");
            }
        }

        var considered = selected
            .Concat(addPaths)
            .Distinct()
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        ValidateClosed(considered, truth.Snapshot, states);

        var consistencyConflicts = considered
            .Where(path => state.Records.TryGetValue(path, out var record)
                && (!baseView.ActiveByPath.TryGetValue(path, out var active)
                    || active.Material.StatementId != record.StatementId))
            .ToImmutableArray();
        if (!consistencyConflicts.IsEmpty)
        {
            return ConflictResult(considered.Length, consistencyConflicts);
        }

        var addedPaths = addPaths
            .Where(path => !state.Records.ContainsKey(path))
            .Distinct()
            .ToImmutableHashSet();
        var changedPaths = considered
            .Where(path => state.Records.TryGetValue(path, out var record)
                && record.StatementId != catalog.ByPath[path].StatementId)
            .ToImmutableHashSet();
        var initialRegeneration = considered
            .Where(path => !baseView.ActiveByPath.TryGetValue(path, out var active)
                || active.Material.StatementId != catalog.ByPath[path].StatementId
                || !active.Material.DeclarationStatementIds.SequenceEqual(
                    catalog.ByPath[path].DeclarationStatementIds))
            .ToImmutableHashSet();
        var regeneration = DescendantClosure(
            initialRegeneration,
            baseView.ActiveByPath.Keys,
            adjacency);
        ValidateClosed(regeneration, truth.Snapshot, states);
        var newEventFiles = BuildAlignedEventFiles(
            regeneration,
            catalog,
            adjacency,
            baseView);
        var replacementFiles = ReplaceEvents(
            acceptedFiles,
            baseView,
            regeneration,
            newEventFiles);
        var replacementEvents = LoadOrderedEvents(
            replacementFiles,
            "aligned frozen ledger");
        _ = ReadView(replacementFiles);
        var stateWritePaths = changedPaths
            .Union(addedPaths)
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        var replacementByPath = replacementEvents.ToImmutableDictionary(
            static item => item.DescriptorPath);
        var stateEvents = stateWritePaths
            .Select(path => replacementByPath[path])
            .ToImmutableArray();

        if (!newEventFiles.IsEmpty || !stateEvents.IsEmpty)
        {
            FrozenLedgerPublication.PublishSnapshot(
                repositoryRoot,
                ledgerPath,
                replacementFiles,
                acceptedFiles,
                stateEvents,
                [],
                "ledger-align");
        }

        return new CommandResult(
            true,
            RenderSummary(
                considered.Length,
                changedPaths.Count,
                addedPaths.Count,
                considered.Length - changedPaths.Count - addedPaths.Count,
                conflicts: 0),
            string.Empty);
    }

    private static void ValidateRequestedPaths(
        AlignOptions options,
        RepositorySnapshot snapshot,
        IReadOnlyDictionary<RepoPath, TruthState> states)
    {
        ValidateClosed(options.Adds, snapshot, states);
    }

    private static void ValidateClosed(
        IEnumerable<RepoPath> paths,
        RepositorySnapshot snapshot,
        IReadOnlyDictionary<RepoPath, TruthState> states)
    {
        foreach (var path in paths.Distinct())
        {
            if (!snapshot.Files.ContainsKey(path))
            {
                throw new InvalidOperationException($"module {path.Value} does not exist");
            }

            if (!states.TryGetValue(path, out var state) || state is not TruthState.Closed)
            {
                var rendered = states.TryGetValue(path, out state) ? state.ToString() : "Unmanaged";
                throw new InvalidOperationException(
                    $"module {path.Value} has TruthState={rendered}, expected Closed");
            }
        }
    }

    private static ImmutableHashSet<RepoPath> DescendantClosure(
        ImmutableHashSet<RepoPath> initial,
        IEnumerable<RepoPath> activePaths,
        IReadOnlyDictionary<RepoPath, ImmutableArray<RepoPath>> adjacency)
    {
        var closure = initial.ToHashSet();
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var path in activePaths)
            {
                if (!closure.Contains(path)
                    && adjacency.TryGetValue(path, out var dependencies)
                    && dependencies.Any(closure.Contains))
                {
                    closure.Add(path);
                    changed = true;
                }
            }
        }

        return closure.ToImmutableHashSet();
    }

    private static ImmutableArray<RepositoryFile> BuildAlignedEventFiles(
        ImmutableHashSet<RepoPath> paths,
        FrozenMaterialCatalog catalog,
        IReadOnlyDictionary<RepoPath, ImmutableArray<RepoPath>> adjacency,
        FrozenLedgerBaseView baseView)
    {
        var eventHashes = new Dictionary<RepoPath, string>();
        var files = ImmutableArray.CreateBuilder<RepositoryFile>();
        foreach (var path in LeanImportAdjacency.DependenciesFirst(paths, adjacency)
            .Where(paths.Contains))
        {
            if (!catalog.ByPath.TryGetValue(path, out var candidate))
            {
                throw new InvalidOperationException(
                    $"canonical Lean report cannot materialize Closed module {path.Value}");
            }

            var prerequisites = adjacency[path]
                .Select(dependency => eventHashes.TryGetValue(dependency, out var eventHash)
                    ? FrozenNodeId.Create(eventHash)
                    : baseView.ActiveByPath.TryGetValue(dependency, out var active)
                        ? FrozenNodeId.Create(active.EventHash)
                        : throw new InvalidOperationException(
                            $"module {path.Value} dependency {dependency.Value} has no accepted Freeze"))
                .OrderBy(static identity => identity.Value, StringComparer.Ordinal)
                .ToImmutableArray();
            var material = candidate with
            {
                FrozenNodeId = FrozenContentAddress.ComputeFrozenNodeId(
                    path,
                    candidate.StatementId,
                    prerequisites),
                PrerequisiteFrozenNodeIds = prerequisites,
            };
            var file = DagLedgerAppendWriter.BuildNewEventFiles(
                [new FrozenLedgerDraft(
                    "Freeze",
                    FrozenLedgerCanonicalWriter.FreezeElement(
                        FrozenLedgerCanonicalWriter.FreezePayload(material)))])[0];
            var generated = FrozenAcceptedEventLoader.LoadFiles([file]) switch
            {
                DagLedgerFilesLoadOutcome.Loaded loaded => loaded.Events[0],
                DagLedgerFilesLoadOutcome.Invalid invalid => throw new FormatException(
                    $"generated event for {path.Value} is invalid: {invalid.Message}"),
                _ => throw new InvalidOperationException("unknown frozen event load outcome"),
            };
            eventHashes.Add(path, generated.EventHash);
            files.Add(file);
        }

        return files.ToImmutable();
    }

    private static ImmutableArray<RepositoryFile> ReplaceEvents(
        ImmutableArray<RepositoryFile> acceptedFiles,
        FrozenLedgerBaseView baseView,
        ImmutableHashSet<RepoPath> paths,
        ImmutableArray<RepositoryFile> replacements)
    {
        var removed = baseView.Events
            .Where(item => item.FreezePayload is not null
                && paths.Contains(RepoPath.CreateKnown(item.FreezePayload.DescriptorSelector)))
            .Select(static item => item.SourcePath)
            .ToImmutableHashSet();
        return acceptedFiles
            .Where(file => !removed.Contains(file.Path))
            .Concat(replacements)
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .ToImmutableArray();
    }

    private static FrozenLedgerBaseView ReadView(IEnumerable<RepositoryFile> files) =>
        FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            files.ToImmutableDictionary(static file => file.Path)));

    private static ImmutableArray<DagLedgerFileEvent> LoadOrderedEvents(
        IEnumerable<RepositoryFile> files,
        string label)
    {
        var loaded = FrozenAcceptedEventLoader.LoadFiles(files) switch
        {
            DagLedgerFilesLoadOutcome.Loaded accepted => accepted.Events,
            DagLedgerFilesLoadOutcome.Invalid invalid => throw new FormatException(
                $"{label} is invalid: {invalid.Message}"),
            _ => throw new InvalidOperationException("unknown frozen event load outcome"),
        };
        if (!DagLedgerLoader.TryOrderClosedDag(
            loaded,
            ImmutableArray<string>.Empty,
            out var ordered))
        {
            throw new FormatException($"{label} is not a closed dependency DAG");
        }

        return ordered;
    }

    private static FrozenStateCatalog ReadStateCatalog(string repositoryRoot)
    {
        var stateRoot = Path.Combine(
            repositoryRoot,
            FrozenStatePath.Root.Replace('/', Path.DirectorySeparatorChar));
        if (!Directory.Exists(stateRoot))
        {
            return FrozenStateCatalog.Load(RepositorySnapshot.Create(
                ImmutableDictionary<RepoPath, RepositoryFile>.Empty));
        }

        var files = Directory
            .EnumerateFiles(stateRoot, "*.json", SearchOption.AllDirectories)
            .Select(path =>
            {
                var relative = Path.GetRelativePath(repositoryRoot, path).Replace('\\', '/');
                if (!RepoPath.TryCreate(relative, out var repoPath))
                {
                    throw new FormatException($"Frozen state path is not canonical: {relative}");
                }

                var bytes = File.ReadAllBytes(path);
                return new RepositoryFile(
                    repoPath,
                    ImmutableArray.CreateRange(bytes),
                    Encoding.UTF8.GetString(bytes));
            })
            .ToImmutableDictionary(static file => file.Path);
        return FrozenStateCatalog.Load(RepositorySnapshot.Create(files));
    }

    private static AlignOptions ParseArguments(
        IReadOnlyList<string> arguments,
        bool appendAlias)
    {
        string? report = null;
        var selectors = ImmutableArray.CreateBuilder<RepoPath>();
        var adds = ImmutableArray.CreateBuilder<RepoPath>();
        var fromAccepted = false;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--candidate-lean-report" when ++index < arguments.Count && report is null:
                    report = arguments[index];
                    break;
                case "--selector" when !appendAlias && ++index < arguments.Count:
                    selectors.Add(ParseModulePath(arguments[index]));
                    break;
                case "--add" when !appendAlias && ++index < arguments.Count:
                    adds.Add(ParseModulePath(arguments[index]));
                    break;
                case "--from-accepted" when !appendAlias && !fromAccepted:
                    fromAccepted = true;
                    break;
                default:
                    throw Usage(appendAlias);
            }
        }

        if (fromAccepted)
        {
            if (report is not null || selectors.Count != 0 || adds.Count != 0)
            {
                throw Usage(appendAlias);
            }
        }
        else if (string.IsNullOrWhiteSpace(report))
        {
            throw Usage(appendAlias);
        }

        return new AlignOptions(
            report,
            selectors.Distinct().ToImmutableArray(),
            adds.Distinct().ToImmutableArray(),
            fromAccepted);
    }

    private static RepoPath ParseModulePath(string value)
    {
        if (!RepoPath.TryCreate(value, out var path))
        {
            throw new InvalidOperationException($"module selector is not canonical: {value}");
        }

        _ = FrozenStatePath.FromModulePath(path);
        return path;
    }

    private static InvalidOperationException Usage(bool appendAlias) => new(
        appendAlias
            ? "USAGE: StrataLint ledger-append --candidate-lean-report FILE"
            : "USAGE: StrataLint ledger-align --candidate-lean-report FILE "
                + "[--selector D5/.../X.lean]... [--add D5/.../X.lean]... "
                + "| ledger-align --from-accepted");

    private static CommandResult ConflictResult(
        int considered,
        ImmutableArray<RepoPath> conflicts) =>
        new(
            false,
            RenderSummary(considered, 0, 0, considered - conflicts.Length, conflicts.Length),
            "LEDGER_ALIGN_FAILED state/event statement_id conflicts: "
                + string.Join(", ", conflicts.Select(static path => path.Value))
                + "\n");

    private static string RenderAcceptedCounts(
        int acceptedSelectors,
        int stateBefore,
        int stateAfter,
        int written,
        int conflicts) =>
        $"accepted_selectors={acceptedSelectors} state_before={stateBefore} "
        + $"state_after={stateAfter} written={written} conflicts={conflicts}\n";

    private static string RenderSummary(
        int selectorsConsidered,
        int changed,
        int added,
        int unchanged,
        int conflicts) =>
        $"LEDGER_ALIGN selectors_considered={selectorsConsidered} changed={changed} "
        + $"added={added} unchanged={unchanged} conflicts={conflicts}\n";

    private static string LedgerPath(string repositoryRoot) => Path.Combine(
        repositoryRoot,
        FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));

    private sealed record AlignOptions(
        string? ReportPath,
        ImmutableArray<RepoPath> Selectors,
        ImmutableArray<RepoPath> Adds,
        bool FromAccepted);
}
