using System.Collections.Immutable;
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
            // Undeclared theory documents are registered from the theory directory itself.
            var (currentRaw, current, document) = DigestionWorkingTree.ReadIngest(
                repository,
                Decode,
                static snapshot => LoadDocument(snapshot),
                DigestionOpaquePathPolicy.TheoryRootPath.TrimEnd('/'));
            var (sourceIds, registrationPaths) = ResolveSources(document, current, options.Sources);
            var plan = ReportFreeDigestionIngestor.Plan(
                document,
                current,
                sourceIds,
                registrationPaths,
                dependencies.AtomizerResolver,
                dependencies.ContentKindAtomizerResolver);
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
            return WriteReportFreeResult(
                repositoryRoot,
                currentRaw,
                document,
                finalRaw,
                plan,
                sourceIds,
                dependencies);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"INGEST_INVALID {exception.Message}\n");
        }
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
        var ledgerUpdates = LedgerAdditions(currentRaw, finalRaw, plan);
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
        var createdCasPaths = WriteCasObjects(repositoryRoot, plan.CasObjects);
        try
        {
            ApplyLedgerAdditionsAtomically(repositoryRoot, ledgerUpdates, dependencies.CommitLedgerFile);
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
        return new ReportFreeOptions(sources.ToImmutable());
    }

    private sealed record ReportFreeOptions(ImmutableArray<string> Sources);
}
