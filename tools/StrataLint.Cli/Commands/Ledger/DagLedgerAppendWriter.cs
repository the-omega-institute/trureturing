using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
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
            var drafts = FrozenLedgerGenerator.MissingFreezes(
                context.Baseline,
                context.Catalog);
            if (drafts.IsEmpty)
            {
                return new CommandResult(
                    true,
                    $"LEDGER_APPEND appended_freezes=0 no catalog reconciliation required "
                    + $"events={context.Baseline.EventCount} head={context.Baseline.HeadHash}\n",
                    string.Empty);
            }

            var pending = BuildNewEventFiles(drafts);
            var prospective = DagLedgerCommandPreparation.ValidateGeneratedEventFiles(
                context.BaseView,
                pending,
                "generated frozen ledger suffix");
            var trustedCandidateReferences = DagLedgerCommandPreparation.ValidateSuffixReferences(
                repository,
                prospective,
                "generated frozen ledger");
            var candidate = FrozenLedger.ValidateCandidate(
                prospective,
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
            WriteEventFiles(context.LedgerPath, pending, context.BaselineFiles);
            var freezes = prospective
                .Where(static item => item.EventType == "Freeze")
                .ToImmutableArray();
            var output = $"LEDGER_APPEND appended_freezes={freezes.Length} "
                + $"events={candidate.EventCount} "
                + $"head={context.BaseView.EventSetRoot(prospective.Select(static item => item.EventHash))}\n"
                + string.Concat(freezes.Select(static item =>
                    $"FROZEN {item.Input!.DescriptorSelector}\n"));
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

    internal static ImmutableArray<RepositoryFile> BuildNewEventFiles(
        IEnumerable<FrozenLedgerDraft> drafts)
    {
        var files = ImmutableArray.CreateBuilder<RepositoryFile>();
        foreach (var draft in drafts)
        {
            var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
                draft.EventType,
                draft.Payload);
            var identity = FrozenLedgerCanonicalWriter.EventIdentity(encoded.Hash);
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
