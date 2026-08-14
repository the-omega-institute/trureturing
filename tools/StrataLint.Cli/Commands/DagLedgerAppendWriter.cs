using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DagLedgerAppendWriter
{
    internal sealed record PendingEventFile(string Path, ImmutableArray<byte> Bytes);

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
                    $"LEDGER_APPEND no missing freezes events={context.Baseline.Events.Length} head={context.Baseline.HeadHash}\n",
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
                context.Baseline.Events.Length);
            var appended = candidate.Events
                .Skip(context.Baseline.Events.Length)
                .OfType<FrozenLedgerEvent.Freeze>()
                .ToImmutableArray();
            var output = $"LEDGER_APPEND appended_freezes={appended.Length} "
                + $"events={candidate.Events.Length} head={candidate.HeadHash}\n"
                + string.Concat(appended.Select(static item => $"FROZEN {item.Payload.NodePath.Value}\n"));
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
                "LEDGER_APPEND_FAILED " + (exception.InnerException ?? exception).Message + "\n");
        }
    }

    internal static void WriteNewEvents(
        string directory,
        IEnumerable<FrozenLedgerLineSyntax> lines,
        int skip = 0) =>
        WriteEventFiles(directory, BuildNewEventFiles(lines, skip));

    internal static IEnumerable<PendingEventFile> PrepareNewEvents(
        string directory,
        IEnumerable<FrozenLedgerLineSyntax> lines,
        int skip = 0)
    {
        foreach (var file in BuildNewEventFiles(lines, skip))
        {
            yield return new PendingEventFile(
                Path.Combine(directory, Path.GetFileName(file.Path.Value)),
                file.RawBytes);
        }
    }

    internal static ImmutableArray<RepositoryFile> BuildNewEventFiles(
        IEnumerable<FrozenLedgerLineSyntax> lines,
        int skip = 0)
    {
        var files = ImmutableArray.CreateBuilder<RepositoryFile>();
        var linearToDagHash = new Dictionary<string, string>(StringComparer.Ordinal);
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
        IEnumerable<RepositoryFile> files)
    {
        var createdPaths = new Stack<string>();
        try
        {
            foreach (var file in files)
            {
                var path = Path.Combine(directory, Path.GetFileName(file.Path.Value));
                using var stream = new FileStream(path, FileMode.CreateNew, FileAccess.Write, FileShare.None);
                createdPaths.Push(path);
                stream.Write(file.RawBytes.AsSpan());
            }
        }
        catch
        {
            RollbackCreatedFiles(createdPaths);
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
}
