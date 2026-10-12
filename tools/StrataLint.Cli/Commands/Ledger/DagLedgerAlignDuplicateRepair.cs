using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class DagLedgerAlignWriter
{
    private static CommandResult RepairDuplicateRegistrations(
        string repositoryRoot,
        IRepositoryGateway repository,
        AlignOptions options)
    {
        var ledgerPath = LedgerPath(repositoryRoot);
        var acceptedFiles = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(ledgerPath);
        _ = LoadEvents(acceptedFiles, "accepted frozen ledger");
        var recordedEvents = acceptedFiles.Select(FrozenLedgerBaseViewReader.ReadEvent).ToImmutableArray();
        var entries = recordedEvents.Select(FrozenLedgerBaseViewReader.ReadFreeze).ToImmutableArray();
        var byPath = entries.ToLookup(static entry => entry.Material.RepoPath);
        var duplicates = byPath.Where(static group => group.Count() > 1)
            .Select(static group => group.Key).ToImmutableHashSet();
        var seeds = options.DuplicateRepairs.ToImmutableHashSet();
        if (!duplicates.SetEquals(seeds))
        {
            throw new InvalidOperationException(
                "duplicate repair requires exactly the duplicated accepted registrations: "
                + string.Join(" ", duplicates.OrderBy(static path => path.Value, StringComparer.Ordinal)
                    .Select(static path => "--repair-duplicate-registration " + path.Value)));
        }

        var requested = seeds.Union(options.Selectors);
        var truth = DagLedgerCommandPreparation.BuildTruthScoped(repository,
            new DagLedgerCommandPreparation.FileLeanReportSource(options.ReportPath!), requested);
        var states = LeanTruthStates.Resolve(truth.Snapshot, truth.Lean);
        var adjacency = LeanImportAdjacency.Build(truth.Snapshot, truth.Lean);
        var currentImports = LeanImportAdjacency.BuildFromSources(truth.Snapshot);
        var repairPaths = seeds;
        while (true)
        {
            var expanded = DescendantClosure(
                FrozenLedgerReplacementClosure.DescendantsFrom(entries, repairPaths),
                byPath.Select(static group => group.Key), currentImports);
            if (expanded.SetEquals(repairPaths)) break;
            repairPaths = expanded;
        }

        var missing = repairPaths.Except(requested).OrderBy(static path => path.Value, StringComparer.Ordinal).ToArray();
        if (missing.Length != 0)
        {
            throw new InvalidOperationException("duplicate repair descendants require explicit --selector: "
                + string.Join(" ", missing.Select(static path => "--selector " + path.Value)));
        }
        if (!requested.SetEquals(repairPaths))
            throw new InvalidOperationException("duplicate repair selectors must be affected frozen descendants only");

        ValidateClosed(repairPaths, truth.Snapshot, states);
        var catalog = FrozenContentAddress.Build(truth.Snapshot, truth.Lean, states, adjacency) switch
        {
            FrozenMaterialOutcome.Accepted accepted => accepted.Capability,
            FrozenMaterialOutcome.Rejected rejected => throw new InvalidOperationException(rejected.Message),
            _ => throw new InvalidOperationException("unknown frozen material outcome"),
        };
        var state = ReadStateCatalog(repositoryRoot);
        foreach (var path in repairPaths.OrderBy(static path => path.Value, StringComparer.Ordinal))
        {
            var candidate = catalog.ByPath[path];
            if (!candidate.AxiomClosure.All(LeanAxiomFacts.IsStandard)
                || !state.Records.TryGetValue(path, out var pin)
                || pin.StatementId != candidate.StatementId
                || byPath[path].Any(entry => entry.Material.StatementId != candidate.StatementId
                    || !entry.Material.DeclarationStatementIds.SequenceEqual(candidate.DeclarationStatementIds)))
            {
                throw new InvalidOperationException(
                    "AUTHORIZATION overall=fail duplicate repair requires unchanged statement/declaration "
                    + $"identities and matching frozen state: {path.Value}");
            }
        }

        var removed = recordedEvents.Where(item => repairPaths.Contains(
                RepoPath.CreateKnown(item.FreezePayload!.DescriptorSelector)))
            .Select(static item => item.SourcePath).ToImmutableHashSet();
        var retainedFiles = acceptedFiles.Where(file => !removed.Contains(file.Path)).ToImmutableArray();
        var retainedView = ReadView(retainedFiles);
        foreach (var path in LeanImportAdjacency.DependenciesFirst(repairPaths, adjacency).Except(repairPaths))
        {
            var candidate = catalog.ByPath[path];
            if (!retainedView.ActiveByPath.TryGetValue(path, out var active)
                || active.Material.StatementId != candidate.StatementId
                || !active.Material.DeclarationStatementIds.SequenceEqual(candidate.DeclarationStatementIds)
                || !state.Records.TryGetValue(path, out var pin)
                || pin.StatementId != candidate.StatementId)
            {
                throw new InvalidOperationException(
                    $"duplicate repair prerequisite identity is missing or changed: {path.Value}");
            }
        }

        var replacements = BuildAlignedEventFiles(repairPaths, catalog, adjacency, retainedView);
        var replacementFiles = retainedFiles.Concat(replacements).ToImmutableArray();
        var replacementEvents = LoadEvents(replacementFiles, "duplicate-repaired frozen ledger");
        _ = ReadView(replacementFiles);
        if (!DagLedgerLoader.TryOrderClosedDag(replacementEvents, [], out _))
            throw new InvalidOperationException("duplicate-repaired frozen ledger does not form a closed dependency DAG");

        FrozenLedgerPublication.PublishSnapshot(repositoryRoot, ledgerPath,
            replacementFiles, acceptedFiles, [], [], "ledger-align --repair-duplicate-registration");
        return new CommandResult(true,
            RenderSummary(repairPaths.Count, 0, 0, repairPaths.Count, 0)
            + $"LEDGER_DUPLICATE_REPAIR duplicate_modules={seeds.Count} "
            + $"replaced_registrations={removed.Count} reattested_modules={repairPaths.Count}\n"
            + "AUTHORIZATION overall=pass\n", string.Empty);
    }
}
