using System.Collections.Immutable;
using System.Security.Cryptography;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record ReportFreeIngestDependencies(
    Func<string, TheoryAtomizer>? AtomizerResolver = null,
    Func<string, TheoryAtomizerWithContentKinds>? ContentKindAtomizerResolver = null,
    Func<ReportFreeDigestionIngestPlan, ReportFreeDigestionIngestPlan>? BeforeValidation = null,
    Action? BeforeCommit = null,
    Action<string, string>? CommitLedgerFile = null);

internal static partial class IngestCommand
{
    internal static CommandResult RunReportFree(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments,
        ReportFreeIngestDependencies? dependencies = null)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(arguments);
        dependencies ??= new ReportFreeIngestDependencies();
        try
        {
            var options = ParseReportFreeArguments(arguments);
            var (currentRaw, current, document) = ReadSelectedSources(repository, options.Sources);
            var (sourceIds, registrationPaths) = ResolveSources(document, current, options.Sources);
            var populated = document.RequireDigestionSources().Where(source => repository.SearchCurrentPaths(
                    [DigestionQuerySelection.Literal(BackfillInventoryLoader.RootPath + source.SourceId)])
                .Any(path => DigestionQuerySelection.IsAtomPath(path) && BackfillInventoryLoader.IsCanonicalPath(path)))
                .Select(static source => source.SourceId).ToHashSet(StringComparer.Ordinal);
            var wholeSourceIds = document.RequireDigestionSources().Where(source => current.TryGetFile(source.SourcePath, out _))
                .Select(source => { current.TryGetFile(source.SourcePath, out var file); return DigestionFingerprint.ComputeOpaque(file!.RawBytes.AsSpan()).RawSha256[7..]; })
                .Distinct(StringComparer.Ordinal).ToArray();
            var wholeSourceRecords = DigestionQuerySelection.ReadAtoms(repository, wholeSourceIds);
            (currentRaw, current, document) = DigestionQuerySelection.Load(DigestionQuerySelection.Merge(currentRaw, wholeSourceRecords.Raw));
            var cache = new Dictionary<(string Id, string Hash), AtomizedTheoryDocument>();
            var kindCache = new Dictionary<(string Id, string Hash), (AtomizedTheoryDocument Document, Dictionary<string, string> Kinds)>();
            Func<string, TheoryAtomizer> atomizers = id => (bytes) =>
            {
                var key = (id, Convert.ToHexStringLower(SHA256.HashData(bytes)));
                if (!cache.TryGetValue(key, out var atomized))
                    cache[key] = atomized = (dependencies.AtomizerResolver ?? (static name => AtomizerRegistry.Require(name).Atomize))(id)(bytes);
                return atomized;
            };
            Func<string, TheoryAtomizerWithContentKinds>? kindAtomizers = dependencies.AtomizerResolver is not null
                && dependencies.ContentKindAtomizerResolver is null ? null : id => (bytes, contentKinds) =>
                {
                    var key = (id, Convert.ToHexStringLower(SHA256.HashData(bytes)));
                    if (!kindCache.TryGetValue(key, out var cached))
                    {
                        var kinds = new Dictionary<string, string>(StringComparer.Ordinal);
                        var atomized = (dependencies.ContentKindAtomizerResolver ?? (static name => AtomizerRegistry.Require(name).AtomizeWithContentKinds))(id)(bytes, kinds);
                        kindCache[key] = cached = (atomized, kinds);
                    }
                    if (contentKinds is not null)
                        foreach (var kind in cached.Kinds) contentKinds[kind.Key] = kind.Value;
                    return cached.Document;
                };
            var plan = ReportFreeDigestionIngestor.Plan(
                document,
                current,
                sourceIds,
                registrationPaths,
                atomizers,
                kindAtomizers,
                populated);
            var existing = DigestionQuerySelection.ReadAtoms(repository, plan.AddedAtomIds.ToArray());
            if (!existing.Document.RequireDigestionEntries().IsEmpty)
            {
                var loaded = DigestionQuerySelection.Load(DigestionQuerySelection.Merge(currentRaw, existing.Raw));
                (currentRaw, current, document) = loaded;
                plan = ReportFreeDigestionIngestor.Plan(document, current, sourceIds, registrationPaths, atomizers, kindAtomizers, populated);
            }
            if (dependencies.BeforeValidation is not null)
            {
                plan = dependencies.BeforeValidation(plan)
                    ?? throw new InvalidOperationException(
                        "report-free ingest pre-write plan hook returned null");
            }

            var finalRaw = AddCasObjects(
                AppendLedger(
                    currentRaw,
                    document,
                    plan),
                plan.CasObjects);
            RequireAppendOnlyWriteSet(currentRaw, document, plan.Document,
                LedgerUpdates(currentRaw, finalRaw, document, plan.Document), plan.CasObjects, plan.AddedAtomIds, sourceIds);
            RequireNewCasIntegrity(document, plan.Document, plan.CasObjects, plan.AddedAtomIds);
            var contextUnavailable = new List<string>();
            var contextIndexes = ImmutableArray.CreateBuilder<DigestionContextPointerIndex>();
            var contextCas = ImmutableArray.CreateBuilder<DigestionCasObject>();
            foreach (var sourceId in sourceIds ?? plan.Document.RequireDigestionSources()
                         .Select(static source => source.SourceId).ToImmutableHashSet(StringComparer.Ordinal))
            {
                if (plan.Fallbacks.Any(fallback => fallback.SourceId == sourceId)) continue;
                var contextInput = DigestionQuerySelection.ReadChains(repository, DigestionQuerySelection.Load(finalRaw));
                contextInput = DigestionQuerySelection.Load(DigestionQuerySelection.Merge(contextInput.Raw,
                    repository.ReadCurrent(contextInput.Document.RequireDigestionEntries().Select(DigestionQuerySelection.CasPath).ToArray())));
                var corrupt = contextInput.Document.RequireDigestionEntries().FirstOrDefault(entry =>
                    contextInput.Snapshot.TryGetFile(DigestionCasStore.RootPath + entry.AtomId, out var blob)
                    && DigestionCasStore.Capture(blob.RawBytes.AsSpan()).Reference != "sha256:" + entry.AtomId);
                if (corrupt is not null)
                {
                    contextUnavailable.Add($"INGEST_CONTEXT_UNAVAILABLE source_id={sourceId} reason=CAS_MISMATCH atom_id={corrupt.AtomId}\n");
                    continue;
                }
                var built = DigestionContextIndexBuilder.Build(contextInput.Snapshot, contextInput.Document, sourceId);
                currentRaw = DigestionQuerySelection.Merge(currentRaw, RawRepositorySnapshot.Create(contextInput.Raw.Entries
                    .Where(entry => IsContextIndexPath(entry.Path))));
                var saved = repository.ReadCurrent(built.Index.Entries.Select(entry => DigestionQuerySelection.Literal(
                    DigestionContextPointerIndex.RelativePath(sourceId, entry.AtomId))).ToArray());
                currentRaw = DigestionQuerySelection.Merge(currentRaw, saved);
                finalRaw = DigestionQuerySelection.Merge(finalRaw, saved);
                var index = built.Index;
                contextIndexes.Add(index);
                contextCas.AddRange(built.CasObjects);
            }
            plan = plan with
            {
                ContextIndexes = contextIndexes.ToImmutable(),
                ContextCasObjects = contextCas
                    .GroupBy(static item => item.Reference, StringComparer.Ordinal)
                    .Select(static group => group.First())
                    .OrderBy(static item => item.RelativePath, StringComparer.Ordinal)
                    .ToImmutableArray(),
            };
            finalRaw = AddCasObjects(finalRaw, plan.ContextCasObjects);
            finalRaw = AddContextIndexes(finalRaw, plan.ContextIndexes);
            var result = WriteReportFreeResult(
                repositoryRoot,
                currentRaw,
                document,
                finalRaw,
                plan,
                sourceIds,
                dependencies);
            return result with { Output = result.Output + string.Concat(contextUnavailable) };
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"INGEST_INVALID {exception.Message}\n");
        }
    }

    private static RawRepositorySnapshot AddContextIndexes(
        RawRepositorySnapshot snapshot,
        IEnumerable<DigestionContextPointerIndex> indexes)
    {
        foreach (var index in indexes) snapshot = DigestionContextPointerStore.Add(snapshot, DigestionContextPointerStore.PreserveSavedGraph(snapshot, index));
        return snapshot;
    }

    private static CommandResult WriteReportFreeResult(
        string repositoryRoot,
        RawRepositorySnapshot currentRaw,
        BackfillInventoryDocument currentDocument,
        RawRepositorySnapshot finalRaw,
        ReportFreeDigestionIngestPlan plan,
        ImmutableHashSet<string>? sourceIds,
        ReportFreeIngestDependencies dependencies)
    {
        var ledgerUpdates = LedgerUpdates(currentRaw, finalRaw, currentDocument, plan.Document);
        RequireAppendOnlyWriteSet(
            currentRaw,
            currentDocument,
            plan.Document,
            ledgerUpdates,
            plan.CasObjects,
            plan.AddedAtomIds,
            sourceIds);
        RequireNewCasIntegrity(currentDocument, plan.Document, plan.CasObjects, plan.AddedAtomIds);
        var openGenres = plan.Document.RequireDigestionSources()
            .Where(source => sourceIds is null || sourceIds.Contains(source.SourceId))
            .SelectMany(static source => source.GenreRegistryCheck.UnregisteredGenres.Select(token =>
                (source.SourceId, Token: token)))
            .OrderBy(static item => item.SourceId, StringComparer.Ordinal)
            .ThenBy(static item => item.Token, StringComparer.Ordinal)
            .ToImmutableArray();
        dependencies.BeforeCommit?.Invoke();
        RequireUnclaimedAtomIds(repositoryRoot, plan.AddedAtomIds);
        var allCasObjects = plan.CasObjects.Concat(plan.ContextCasObjects)
            .GroupBy(static item => item.Reference, StringComparer.Ordinal)
            .Select(static group => group.First())
            .OrderBy(static item => item.RelativePath, StringComparer.Ordinal)
            .ToImmutableArray();
        var createdCasPaths = WriteCasObjects(repositoryRoot, allCasObjects);
        try
        {
            ApplyLedgerUpdatesAtomically(repositoryRoot, currentRaw, ledgerUpdates, dependencies.CommitLedgerFile,
                () => RequireReportFreeInputs(repositoryRoot, currentRaw, ledgerUpdates));
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            RollbackCasObjects(createdCasPaths, exception);
            throw;
        }

        return new CommandResult(
            true,
            $"INGEST residual_open_added={plan.ResidualOpenAdded} "
            + $"skipped_existing={plan.SkippedExisting} "
            + $"coarse_fallbacks={plan.Fallbacks.Length} "
            + $"open_genres={openGenres.Length} "
            + $"cas_objects_written={createdCasPaths.Length} "
            + $"ledger_changed={(ledgerUpdates.Length > 0).ToString().ToLowerInvariant()}\n"
            + string.Concat(openGenres.Select(static item =>
                $"INGEST_OPEN_GENRE source={item.SourceId} "
                + $"token={System.Text.Json.JsonSerializer.Serialize(item.Token)}\n"))
            + string.Concat(plan.Fallbacks.Select(static fallback =>
                $"INGEST_FALLBACK source={fallback.SourceId} reason={fallback.Reason}\n"))
            + (plan.Fallbacks.Length == 0
                ? string.Empty
                : $"INGEST_INCOMPLETE {plan.Fallbacks.Length} source"
                    + (plan.Fallbacks.Length == 1 ? string.Empty : "s")
                    + " registered without being atomised: "
                    + string.Join(", ", plan.Fallbacks.Select(static item => item.SourceId))
                    + "\n"),
            string.Empty);
    }

    private static ReportFreeOptions ParseReportFreeArguments(IReadOnlyList<string> arguments)
    {
        var sources = ImmutableArray.CreateBuilder<string>();
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (arguments[index] != "--source")
                throw SourceUsage($"unexpected argument '{arguments[index]}'");
            if (index + 1 == arguments.Count)
                throw SourceUsage("--source missing value");
            if (string.IsNullOrWhiteSpace(arguments[index + 1]))
                throw SourceUsage($"invalid --source selector '{arguments[index + 1]}'");
            sources.Add(arguments[index + 1]);
        }
        if (sources.Count == 0) throw SourceUsage("at least one --source is required");
        return new ReportFreeOptions(sources.ToImmutable());
    }

    private sealed record ReportFreeOptions(ImmutableArray<string> Sources);
}
