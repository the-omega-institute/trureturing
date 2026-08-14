using System.Collections.Immutable;
using System.Runtime.ExceptionServices;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DagLedgerAppendWriter
{
    internal sealed record PublishedRollback(
        ImmutableArray<string> RolledBackPaths,
        string? StoppedPath,
        Exception? Failure);

    private sealed record PendingEvent(
        string EventType,
        string ModulePath,
        string Identity,
        string FinalPath,
        ImmutableArray<byte> Bytes);

    internal static CommandResult Append(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 2 || arguments[0] != "--candidate-lean-report")
            {
                throw new InvalidOperationException(
                    "USAGE: StrataLint ledger-append --candidate-lean-report FILE");
            }

            var context = DagLedgerCommandPreparation.Prepare(
                repositoryRoot,
                repository,
                arguments[1]);
            var candidateBytes = FrozenLedgerGenerator.ReconcileToCatalog(
                context.Baseline,
                context.Catalog);
            if (candidateBytes.AsSpan().SequenceEqual(context.BaselineBytes))
            {
                return new CommandResult(
                    true,
                    $"LEDGER_APPEND appended_reattests=0 appended_freezes=0 no catalog reconciliation required "
                    + $"events={context.Baseline.Events.Length} head={context.Baseline.HeadHash}\n",
                    string.Empty);
            }

            var candidateSyntax = DagLedgerCommandPreparation.LoadLedger(
                candidateBytes.AsSpan(),
                "generated frozen ledger");
            var candidateReferences = DagLedgerCommandPreparation.ScanReferences(
                candidateSyntax,
                "generated frozen ledger");
            var trustedCandidateReferences = repository.ValidateFrozenReferences(candidateReferences);
            var candidate = FrozenLedger.ValidateCandidate(
                candidateSyntax,
                context.Baseline,
                context.Catalog,
                trustedCandidateReferences) switch
            {
                FrozenLedgerValidationOutcome.Accepted accepted => accepted.Capability,
                FrozenLedgerValidationOutcome.Rejected rejected => throw new InvalidOperationException(
                    "generated frozen ledger is invalid: " + rejected.Message),
                _ => throw new InvalidOperationException("unknown ledger validation outcome"),
            };
            if (!DagLedgerCommandPreparation.LoadLedgerDirectory(context.LedgerPath, "existing frozen ledger")
                    .RawBytes.AsSpan().SequenceEqual(context.BaselineBytes))
            {
                throw new InvalidOperationException("accepted event files changed while ledger-append was validating them");
            }

            var scratchWarning = WriteNewEvents(
                context.LedgerPath,
                candidateSyntax.Lines,
                context.Baseline.Events.Length,
                context.BaselineBytes);
            var appended = candidate.Events.Skip(context.Baseline.Events.Length).ToImmutableArray();
            var reattests = appended
                .OfType<FrozenLedgerEvent.Reattest>()
                .ToImmutableArray();
            var freezes = appended
                .OfType<FrozenLedgerEvent.Freeze>()
                .ToImmutableArray();
            var output = $"LEDGER_APPEND appended_reattests={reattests.Length} appended_freezes={freezes.Length} "
                + $"events={candidate.Events.Length} head={candidate.HeadHash}\n"
                + string.Concat(reattests.Select(item =>
                    $"REATTESTED {context.Baseline.ActiveEntries[item.Payload.CaseId].Material.RepoPath.Value}\n"))
                + string.Concat(freezes.Select(static item => $"FROZEN {item.Payload.NodePath.Value}\n"));
            return new CommandResult(true, output, scratchWarning);
        }
        // Preparation marks report and repository faults now. Without these two the wrapped
        // forms escape this catch and the command loses its own diagnostic.
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
                string.Empty,
                RenderFailure("LEDGER_APPEND_FAILED", exception));
        }
    }

    internal static string WriteNewEvents(
        string directory,
        IEnumerable<FrozenLedgerLineSyntax> lines,
        int skip = 0,
        byte[]? expectedBaselineBytes = null)
    {
        Directory.CreateDirectory(directory);
        var lockPath = Path.Combine(directory, ".ledger-write.lock");
        using var publicationLock = AcquirePublicationLock(lockPath);
        if (expectedBaselineBytes is not null
            && !DagLedgerCommandPreparation.LoadLedgerDirectory(
                    directory,
                    "existing frozen ledger").RawBytes.AsSpan().SequenceEqual(expectedBaselineBytes))
        {
            throw new InvalidOperationException(
                "accepted event files changed while the ledger command was validating them");
        }

        ReapStaleStagingDirectories(directory);

        var linearToDagHash = new Dictionary<string, string>(StringComparer.Ordinal);
        var pending = ImmutableArray.CreateBuilder<PendingEvent>();
        var sequence = 0;
        foreach (var line in lines)
        {
            var payload = line.Value.GetProperty("payload");
            if (payload.TryGetProperty("previous_attestation_event_hash", out var previous))
            {
                var rewritten = JsonNode.Parse(payload.GetRawText())!.AsObject();
                rewritten["previous_attestation_event_hash"] = linearToDagHash[previous.GetString()!];
                payload = JsonSerializer.SerializeToElement(rewritten);
            }

            var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
                line.Value.GetProperty("event_type").GetString()!,
                payload);
            linearToDagHash.Add(line.Value.GetProperty("event_hash").GetString()!, encoded.Hash);
            if (sequence++ < skip)
            {
                continue;
            }

            var eventType = line.Value.GetProperty("event_type").GetString()!;
            var identity = FrozenLedgerCanonicalWriter.EventIdentity(
                eventType,
                payload,
                encoded.Hash);
            pending.Add(new PendingEvent(
                eventType,
                EventModulePath(eventType, payload),
                identity,
                Path.Combine(directory, identity[7..] + ".json"),
                encoded.Bytes));
        }

        var planned = pending.ToImmutable();
        foreach (var duplicate in planned.GroupBy(static item => item.FinalPath, StringComparer.Ordinal)
            .Where(static group => group.Count() > 1))
        {
            var modules = string.Join(", ", duplicate.Select(static item => item.ModulePath));
            throw new IOException(
                $"Cannot publish frozen-ledger batch because identity {duplicate.First().Identity} "
                + $"is planned more than once for modules {modules}.");
        }

        foreach (var item in planned)
        {
            if (File.Exists(item.FinalPath))
            {
                throw ShardCollision(item);
            }
        }

        if (planned.IsEmpty)
        {
            return string.Empty;
        }

        // A filesystem has no atomic commit spanning these shard renames. The lock serializes the
        // publication phase; read/validate remains optimistic, with the in-lock baseline comparison
        // above closing that window. Suffix-only compensation makes each publication a restartable
        // prefix transaction: at every externally recoverable failure the directory is a valid prefix.
        var stagingDirectory = Path.Combine(directory, $".ledger-stage-{Guid.NewGuid():N}");
        var published = new List<string>(planned.Length);
        try
        {
            Directory.CreateDirectory(stagingDirectory);
            foreach (var item in planned)
            {
                var stagedPath = Path.Combine(stagingDirectory, Path.GetFileName(item.FinalPath));
                using var stream = new FileStream(
                    stagedPath,
                    FileMode.CreateNew,
                    FileAccess.Write,
                    FileShare.None);
                stream.Write(item.Bytes.AsSpan());
                stream.Flush(flushToDisk: true);
            }

            foreach (var item in planned)
            {
                var stagedPath = Path.Combine(stagingDirectory, Path.GetFileName(item.FinalPath));
                try
                {
                    File.Move(stagedPath, item.FinalPath);
                    published.Add(item.FinalPath);
                }
                catch (IOException) when (File.Exists(item.FinalPath))
                {
                    throw ShardCollision(item);
                }
            }
        }
        catch (Exception failure)
        {
            var rollback = RollbackPublishedPrefix(published);
            var scratchFailure = CleanupAfterFailedPublication(stagingDirectory);
            if (rollback.Failure is not null || scratchFailure is not null)
            {
                throw PublicationFailure(failure, published, rollback, scratchFailure);
            }

            ExceptionDispatchInfo.Capture(failure).Throw();
            throw;
        }

        // All shard moves have completed at this point. Scratch cleanup is operational hygiene,
        // not part of the ledger commit point, and must never roll a successful publication back.
        return CleanupAfterSuccessfulPublication(stagingDirectory);
    }

    internal static PublishedRollback RollbackPublishedPrefix(IReadOnlyList<string> published)
    {
        var rolledBack = ImmutableArray.CreateBuilder<string>();
        for (var index = published.Count - 1; index >= 0; index--)
        {
            var path = published[index];
            try
            {
                File.Delete(path);
                rolledBack.Add(path);
            }
            catch (Exception failure) when (failure is IOException or UnauthorizedAccessException)
            {
                return new PublishedRollback(rolledBack.ToImmutable(), path, failure);
            }
        }

        return new PublishedRollback(rolledBack.ToImmutable(), null, null);
    }

    internal static string CleanupAfterSuccessfulPublication(string stagingDirectory)
    {
        try
        {
            Directory.Delete(stagingDirectory);
            return string.Empty;
        }
        catch (Exception failure) when (failure is IOException or UnauthorizedAccessException)
        {
            return "LEDGER_SCRATCH_CLEANUP_FAILED publication_succeeded=true scratch="
                + $"{stagingDirectory}: {failure.Message}\n";
        }
    }

    internal static string RenderFailure(string marker, Exception exception)
    {
        var detail = exception.InnerException is null
            ? exception.Message
            : exception.Message + " Cause: " + exception.InnerException.Message;
        return marker + " " + detail + "\n";
    }

    internal static FileStream AcquirePublicationLock(string lockPath)
    {
        try
        {
            return new FileStream(
                lockPath,
                FileMode.OpenOrCreate,
                FileAccess.ReadWrite,
                FileShare.None);
        }
        catch (Exception failure) when (failure is IOException or UnauthorizedAccessException)
        {
            throw new IOException(
                $"Another frozen-ledger publication owns the writer lock {lockPath}.",
                failure);
        }
    }

    private static void ReapStaleStagingDirectories(string directory)
    {
        foreach (var stagingDirectory in Directory.EnumerateDirectories(
            directory,
            ".ledger-stage-*",
            SearchOption.TopDirectoryOnly))
        {
            try
            {
                Directory.Delete(stagingDirectory, recursive: true);
            }
            catch (Exception failure) when (failure is IOException or UnauthorizedAccessException)
            {
                throw new IOException(
                    "LEDGER_SCRATCH_CLEANUP_FAILED publication_succeeded=false stale_scratch="
                    + $"{stagingDirectory}: {failure.Message}",
                    failure);
            }
        }
    }

    private static Exception? CleanupAfterFailedPublication(string stagingDirectory)
    {
        try
        {
            if (Directory.Exists(stagingDirectory))
            {
                Directory.Delete(stagingDirectory, recursive: true);
            }

            return null;
        }
        catch (Exception failure) when (failure is IOException or UnauthorizedAccessException)
        {
            return failure;
        }
    }

    internal static IOException PublicationFailure(
        Exception publicationFailure,
        IReadOnlyList<string> published,
        PublishedRollback rollback,
        Exception? scratchFailure)
    {
        var messages = new List<string>();
        if (rollback.Failure is not null)
        {
            var retainedCount = published.Count - rollback.RolledBackPaths.Length;
            messages.Add(
                "LEDGER_ROLLBACK_INCOMPLETE frozen-ledger batch publication failed and rollback "
                + "was incomplete; deletion stopped before any earlier shard was touched. "
                + $"published={RenderPaths(published)} "
                + $"rolled_back={RenderPaths(rollback.RolledBackPaths)} "
                + $"rollback_stopped_at={Path.GetFileName(rollback.StoppedPath!)} "
                + $"retained_prefix={RenderPaths(published.Take(retainedCount))}");
        }

        if (scratchFailure is not null)
        {
            messages.Add(
                "LEDGER_SCRATCH_CLEANUP_FAILED publication_succeeded=false scratch directory "
                + $"could not be removed: {scratchFailure.Message}");
        }

        var causes = new List<Exception> { publicationFailure };
        if (rollback.Failure is not null)
        {
            causes.Add(rollback.Failure);
        }

        if (scratchFailure is not null)
        {
            causes.Add(scratchFailure);
        }

        return new IOException(
            string.Join(' ', messages),
            new AggregateException(causes));
    }

    private static string RenderPaths(IEnumerable<string> paths) =>
        "[" + string.Join(',', paths.Select(Path.GetFileName)) + "]";

    // OPEN(#1770 A3): frozen-node identity is not injective over ledger events, so returning to
    // prior frozen bytes can collide. Recovery guidance needs a separate design; do not treat
    // byte churn in Lean source as the resolved naming protocol.
    private static IOException ShardCollision(PendingEvent item) => new(
        $"Cannot publish {item.EventType} for module {item.ModulePath}: frozen-ledger shard "
        + $"{Path.GetFileName(item.FinalPath)} already exists, so frozen-node identity "
        + $"{item.Identity} was previously recorded (for example, the module returned to an "
        + "earlier frozen byte state). Use a byte-distinct Closed representation and rerun the "
        + "ledger command; do not delete or rewrite the accepted shard.");

    private static string EventModulePath(string eventType, JsonElement payload)
    {
        if (eventType == "Freeze"
            && payload.TryGetProperty("node_path", out var nodePath))
        {
            return nodePath.GetString()!;
        }

        var inputName = eventType == FrozenLedger.EnvironmentRecoordinateEventType
            ? "new_input"
            : "input";
        if (payload.TryGetProperty(inputName, out var input)
            && input.TryGetProperty("descriptor_selector", out var selector))
        {
            return selector.GetString()!;
        }

        return payload.TryGetProperty("case_id", out var caseId)
            ? $"case {caseId.GetString()}"
            : eventType;
    }

}
