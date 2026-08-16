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
            var trustedCandidateReferences = DagLedgerCommandPreparation.ValidateSuffixReferences(
                repository,
                candidateSyntax,
                context.Baseline,
                "generated frozen ledger");
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
            RequireUnchangedBaseline(context.LedgerPath, context.BaselineFiles, "ledger-append");

            WriteNewEvents(
                context.LedgerPath,
                candidateSyntax.Lines,
                context.Baseline.Events.Length,
                context.BaselineFiles,
                context.BaselineSyntax);
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
        ImmutableArray<RepositoryFile> expectedBaselineFiles = default,
        FrozenLedgerSyntax? existingSyntax = null) =>
        WriteEventFiles(
            directory,
            BuildNewEventFiles(lines, skip, existingSyntax),
            expectedBaselineFiles);

    internal static ImmutableArray<RepositoryFile> BuildNewEventFiles(
        IEnumerable<FrozenLedgerLineSyntax> lines,
        int skip = 0,
        FrozenLedgerSyntax? existingSyntax = null)
    {
        var files = ImmutableArray.CreateBuilder<RepositoryFile>();
        var linearToDagHash = new Dictionary<string, string>(StringComparer.Ordinal);
        var existingDagHashByLinearHash = existingSyntax?.Lines
            .Where(static line => line.SourceDagEventHash is not null)
            .ToDictionary(
                static line => line.Value.GetProperty("event_hash").GetString()!,
                static line => line.SourceDagEventHash!,
                StringComparer.Ordinal)
            ?? new Dictionary<string, string>(StringComparer.Ordinal);
        var sequence = 0;
        foreach (var line in lines)
        {
            var eventType = line.Value.GetProperty("event_type").GetString()!;
            var payload = line.Value.GetProperty("payload");
            var linearEventHash = line.Value.GetProperty("event_hash").GetString()!;
            if (sequence < skip
                && existingDagHashByLinearHash.TryGetValue(linearEventHash, out var existingDagHash))
            {
                linearToDagHash.Add(linearEventHash, existingDagHash);
                sequence++;
                continue;
            }

            if (payload.TryGetProperty("previous_attestation_event_hash", out var previous))
            {
                var rewritten = JsonNode.Parse(payload.GetRawText())!.AsObject();
                rewritten["previous_attestation_event_hash"] = linearToDagHash[previous.GetString()!];
                payload = JsonSerializer.SerializeToElement(rewritten);
            }

            var schemaVersion = sequence < skip && !payload.TryGetProperty("axiom_closure", out _)
                ? 2
                : FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion;
            var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(eventType, payload, schemaVersion);
            linearToDagHash.Add(linearEventHash, encoded.Hash);
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
        ImmutableArray<RepositoryFile> expectedBaselineFiles = default)
    {
        var lockPath = Path.Combine(directory, ".ledger-write.lock");
        using var publicationLock = AcquirePublicationLock(lockPath);
        if (!expectedBaselineFiles.IsDefault
            && !LedgerDirectoryMatches(directory, expectedBaselineFiles))
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

    internal static void RequireUnchangedBaseline(
        string directory,
        ImmutableArray<RepositoryFile> expectedFiles,
        string command)
    {
        if (!LedgerDirectoryMatches(directory, expectedFiles))
        {
            throw new InvalidOperationException(
                $"accepted event files changed while {command} was validating them");
        }
    }

    private static bool LedgerDirectoryMatches(
        string directory,
        ImmutableArray<RepositoryFile> expectedFiles)
    {
        var actual = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(directory);
        if (actual.Length != expectedFiles.Length)
        {
            return false;
        }

        var expectedByPath = expectedFiles.ToDictionary(static file => file.Path);
        return actual.All(file => expectedByPath.TryGetValue(file.Path, out var expected)
            && file.RawBytes.AsSpan().SequenceEqual(expected.RawBytes.AsSpan()));
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
