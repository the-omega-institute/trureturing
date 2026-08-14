using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DagLedgerAppendWriter
{
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
            var candidateBytes = FrozenLedgerGenerator.AppendMissingFreezes(
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

            WriteNewEvents(
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
            return new CommandResult(true, output, string.Empty);
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

    internal static void WriteNewEvents(
        string directory,
        IEnumerable<FrozenLedgerLineSyntax> lines,
        int skip = 0,
        byte[]? expectedBaselineBytes = null) =>
        WriteEventFiles(
            directory,
            BuildNewEventFiles(lines, skip),
            expectedBaselineBytes);

    internal static ImmutableArray<RepositoryFile> BuildNewEventFiles(
        IEnumerable<FrozenLedgerLineSyntax> lines,
        int skip = 0)
    {
        var files = ImmutableArray.CreateBuilder<RepositoryFile>();
        var linearToDagHash = new Dictionary<string, string>(StringComparer.Ordinal);
        var sequence = 0;
        foreach (var line in lines)
        {
            var eventType = line.Value.GetProperty("event_type").GetString()!;
            var payload = line.Value.GetProperty("payload");
            if (payload.TryGetProperty("previous_attestation_event_hash", out var previous))
            {
                var rewritten = JsonNode.Parse(payload.GetRawText())!.AsObject();
                rewritten["previous_attestation_event_hash"] = linearToDagHash[previous.GetString()!];
                payload = JsonSerializer.SerializeToElement(rewritten);
            }

            var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
                eventType,
                payload);
            linearToDagHash.Add(line.Value.GetProperty("event_hash").GetString()!, encoded.Hash);
            if (sequence++ < skip)
            {
                continue;
            }

            var identity = FrozenLedgerCanonicalWriter.EventIdentity(
                eventType,
                payload,
                encoded.Hash);
            var path = RepoPath.CreateKnown(
                $"{FrozenLedgerChangeClassifier.AcceptedRoot}/{identity[7..]}.json");
            files.Add(new RepositoryFile(
                path,
                encoded.Bytes,
                Encoding.UTF8.GetString(encoded.Bytes.AsSpan())));
        }

        return files.ToImmutable();
    }

    internal static void WriteEventFiles(
        string directory,
        IEnumerable<RepositoryFile> files,
        byte[]? expectedBaselineBytes = null)
    {
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
        var planned = files.ToImmutableArray();
        if (planned.IsEmpty)
        {
            return;
        }

        var stagingDirectory = Path.Combine(directory, $".ledger-stage-{Guid.NewGuid():N}");
        var createdPaths = new Stack<string>();
        try
        {
            Directory.CreateDirectory(stagingDirectory);
            foreach (var file in planned)
            {
                var stagedPath = Path.Combine(stagingDirectory, Path.GetFileName(file.Path.Value));
                using var stream = new FileStream(
                    stagedPath,
                    FileMode.CreateNew,
                    FileAccess.Write,
                    FileShare.None);
                stream.Write(file.RawBytes.AsSpan());
                stream.Flush(flushToDisk: true);
            }

            foreach (var file in planned)
            {
                var fileName = Path.GetFileName(file.Path.Value);
                var stagedPath = Path.Combine(stagingDirectory, fileName);
                var finalPath = Path.Combine(directory, fileName);
                File.Move(stagedPath, finalPath);
                createdPaths.Push(finalPath);
            }

            Directory.Delete(stagingDirectory);
        }
        catch
        {
            RollbackCreatedFiles(createdPaths);
            CleanupStagingDirectory(stagingDirectory);
            throw;
        }
    }

    internal static void RollbackCreatedFiles(IEnumerable<string> createdPaths)
    {
        foreach (var path in createdPaths)
        {
            try
            {
                File.Delete(path);
            }
            catch (IOException)
            {
            }
            catch (UnauthorizedAccessException)
            {
            }
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
            Directory.Delete(stagingDirectory, recursive: true);
        }
    }

    private static void CleanupStagingDirectory(string stagingDirectory)
    {
        try
        {
            if (Directory.Exists(stagingDirectory))
            {
                Directory.Delete(stagingDirectory, recursive: true);
            }
        }
        catch (IOException)
        {
        }
        catch (UnauthorizedAccessException)
        {
        }
    }
}
