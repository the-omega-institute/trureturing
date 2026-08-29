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

            var baselineFiles = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(
                Path.Combine(
                    repositoryRoot,
                    FrozenLedgerChangeClassifier.AcceptedRoot.Replace(
                        '/',
                        Path.DirectorySeparatorChar)));
            var legacyFiles = baselineFiles.Where(IsLegacyEventFile).ToImmutableArray();
            var trustedBaselineFiles = legacyFiles.IsEmpty
                ? default
                : baselineFiles.Except(legacyFiles).ToImmutableArray();
            var replacesEntireLegacyLedger = !legacyFiles.IsEmpty && trustedBaselineFiles.IsEmpty;
            var committedLegacyFiles = replacesEntireLegacyLedger
                ? ReadCommittedLegacyLedger(repository)
                : ImmutableArray<RepositoryFile>.Empty;
            if (replacesEntireLegacyLedger
                && !LedgerFileSetsEqual(baselineFiles, committedLegacyFiles))
            {
                throw new InvalidOperationException(
                    "entirely legacy ledger does not match the committed baseline byte-for-byte");
            }

            var context = DagLedgerCommandPreparation.Prepare(
                repositoryRoot,
                repository,
                arguments[1],
                trustedBaselineFiles: trustedBaselineFiles);
            if (replacesEntireLegacyLedger)
            {
                RequireLegacyStatementIdentityContinuity(committedLegacyFiles, context.Catalog);
            }

            var drafts = FrozenLedgerGenerator.MissingFreezes(
                context.Baseline,
                context.Catalog);
            if (drafts.IsEmpty && legacyFiles.IsEmpty)
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
            var candidate = FrozenLedger.ValidateCandidate(
                prospective,
                context.Baseline,
                context.Catalog) switch
            {
                FrozenLedgerValidationOutcome.Accepted accepted => accepted.Capability,
                FrozenLedgerValidationOutcome.Rejected rejected => throw new InvalidOperationException(
                    "generated frozen ledger is invalid: " + rejected.Message),
                _ => throw new InvalidOperationException("unknown ledger validation outcome"),
            };
            if (legacyFiles.IsEmpty)
            {
                RequireUnchangedBaseline(context.LedgerPath, context.BaselineFiles, "ledger-append");
                WriteEventFiles(context.LedgerPath, pending, context.BaselineFiles);
            }
            else
            {
                ReplaceEventFiles(
                    context.LedgerPath,
                    trustedBaselineFiles.Concat(pending).ToImmutableArray(),
                    context.BaselineFiles);
            }
            var freezes = prospective
                .Where(static item => item.EventType == "Freeze")
                .ToImmutableArray();
            var output = $"LEDGER_APPEND appended_freezes={freezes.Length} "
                + $"events={candidate.EventCount} "
                + $"head={context.BaseView.EventSetRoot(prospective.Select(static item => item.EventHash))}\n"
                + string.Concat(freezes.Select(static item =>
                    $"FROZEN {item.DescriptorPath.Value}\n"));
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

    internal static bool IsLegacyEventFile(RepositoryFile file)
    {
        try
        {
            using var document = JsonDocument.Parse(file.RawBytes.ToArray());
            var root = document.RootElement;
            if (!root.TryGetProperty("schema_version", out var schema)
                || !schema.TryGetInt32(out var version)
                || !LegacyFrozenLedgerEventSemantics.IsLegacySchemaVersion(version)
                || !root.TryGetProperty("event_type", out var eventType)
                || eventType.ValueKind != JsonValueKind.String)
            {
                return false;
            }

            return true;
        }
        catch (JsonException)
        {
            return false;
        }
    }

    private static ImmutableArray<RepositoryFile> ReadCommittedLegacyLedger(
        IRepositoryGateway repository)
    {
        var identity = DagLedgerCommandPreparation.Ask(repository.ResolveCurrentRevision);
        var raw = DagLedgerCommandPreparation.Ask(() => repository.ReadRevision(identity.Revision));
        var files = raw.Entries
            .Where(static entry => FrozenLedgerChangeClassifier.IsAcceptedEventPath(entry.Path))
            .Select(static entry => new RepositoryFile(
                RepoPath.CreateKnown(entry.Path),
                entry.Bytes,
                Encoding.UTF8.GetString(entry.Bytes.AsSpan()),
                gitBlobOid: entry.GitBlobOid))
            .ToImmutableArray();
        if (files.IsEmpty || files.Any(static file => !IsLegacyEventFile(file)))
        {
            throw new InvalidOperationException(
                "committed baseline is not the entirely legacy ledger being upgraded");
        }

        return files;
    }

    private static bool LedgerFileSetsEqual(
        ImmutableArray<RepositoryFile> left,
        ImmutableArray<RepositoryFile> right)
    {
        var orderedLeft = left.OrderBy(static file => file.Path.Value, StringComparer.Ordinal).ToArray();
        var orderedRight = right.OrderBy(static file => file.Path.Value, StringComparer.Ordinal).ToArray();
        return orderedLeft.Length == orderedRight.Length
            && orderedLeft.Zip(orderedRight).All(static pair =>
                pair.First.Path == pair.Second.Path
                && pair.First.RawBytes.AsSpan().SequenceEqual(pair.Second.RawBytes.AsSpan()));
    }

    private static void RequireLegacyStatementIdentityContinuity(
        ImmutableArray<RepositoryFile> legacyFiles,
        FrozenMaterialCatalog catalog)
    {
        var recordedByPath = new Dictionary<RepoPath, LegacyFrozenStatementIdentity>();
        foreach (var file in legacyFiles)
        {
            using var document = JsonDocument.Parse(file.RawBytes.ToArray());
            var root = document.RootElement;
            var eventType = RequiredLegacyString(root, "event_type", "legacy event");
            if (LegacyFrozenLedgerEventSemantics.IsIdentityNeutral(eventType))
            {
                continue;
            }

            if (eventType != "Freeze"
                || !root.TryGetProperty("payload", out var payload)
                || payload.ValueKind != JsonValueKind.Object
                || !payload.TryGetProperty("input", out var input)
                || input.ValueKind != JsonValueKind.Object)
            {
                throw new FormatException("committed legacy ledger contains an unsupported event");
            }

            var selector = RequiredLegacyString(input, "descriptor_selector", "legacy Freeze input");
            if (!RepoPath.TryCreate(selector, out var path))
            {
                throw new FormatException("legacy Freeze descriptor_selector is not a canonical path");
            }

            var statement = RequiredLegacyStatementId(payload, "statement_id", "legacy Freeze");
            if (!payload.TryGetProperty("declaration_statement_ids", out var declarationValue)
                || declarationValue.ValueKind != JsonValueKind.Array)
            {
                throw new FormatException("legacy Freeze declaration_statement_ids is not an array");
            }

            var declarations = declarationValue.EnumerateArray().Select(item =>
                new FrozenDeclarationStatement(
                    RequiredLegacyString(item, "declaration_name_key", "legacy declaration"),
                    RequiredLegacyString(item, "kind", "legacy declaration"),
                    RequiredLegacyStatementId(item, "statement_id", "legacy declaration")))
                .ToImmutableArray();
            if (!recordedByPath.TryAdd(
                path,
                new LegacyFrozenStatementIdentity(path, statement, declarations)))
            {
                throw new FormatException($"committed legacy ledger contains duplicate Freeze path {path.Value}");
            }
        }

        if (recordedByPath.Count == 0)
        {
            throw new FormatException("committed legacy ledger contains no Freeze identities");
        }

        var mismatch = LegacyFrozenLedgerStatementIdentityContinuity.FirstMismatch(
            recordedByPath.Values,
            catalog);
        if (mismatch is not null)
        {
            throw new InvalidOperationException(
                $"Active module {mismatch.Value} statement identity changed; append Revoke before rerunning ledger-append.");
        }
    }

    private static string RequiredLegacyString(JsonElement value, string name, string label)
    {
        if (!value.TryGetProperty(name, out var property)
            || property.ValueKind != JsonValueKind.String
            || property.GetString() is not { } text)
        {
            throw new FormatException($"{label} {name} is not a string");
        }

        return text;
    }

    private static StatementId RequiredLegacyStatementId(
        JsonElement value,
        string name,
        string label)
    {
        var statement = RequiredLegacyString(value, name, label);
        return FrozenHashSyntax.IsSha256(statement)
            ? StatementId.Create(statement)
            : throw new FormatException($"{label} {name} is malformed");
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

    internal static void DeleteEventFiles(
        string directory,
        ImmutableArray<RepositoryFile> files,
        ImmutableArray<RepositoryFile> expectedBaselineFiles)
    {
        var lockPath = Path.Combine(directory, ".ledger-write.lock");
        using var publicationLock = AcquirePublicationLock(lockPath);
        if (!LedgerDirectoryMatches(directory, expectedBaselineFiles))
        {
            throw new InvalidOperationException(
                "accepted event files changed while ledger-revoke was validating them");
        }

        ReapStaleStagingDirectories(directory);
        if (files.IsEmpty)
        {
            return;
        }

        var stagingDirectory = Path.Combine(directory, $".ledger-stage-{Guid.NewGuid():N}");
        var moved = new Stack<(string Staged, string Original)>();
        try
        {
            Directory.CreateDirectory(stagingDirectory);
            foreach (var file in files.OrderBy(static file => file.Path.Value, StringComparer.Ordinal))
            {
                var original = Path.Combine(directory, Path.GetFileName(file.Path.Value));
                var staged = Path.Combine(stagingDirectory, Path.GetFileName(file.Path.Value));
                File.Move(original, staged);
                moved.Push((staged, original));
            }

            Directory.Delete(stagingDirectory, recursive: true);
        }
        catch
        {
            while (moved.TryPop(out var item))
            {
                if (File.Exists(item.Staged))
                {
                    File.Move(item.Staged, item.Original);
                }
            }

            CleanupStagingDirectory(stagingDirectory);
            throw;
        }
    }

    internal static void ReplaceEventFiles(
        string directory,
        ImmutableArray<RepositoryFile> files,
        ImmutableArray<RepositoryFile> expectedBaselineFiles)
    {
        var lockPath = Path.Combine(directory, ".ledger-write.lock");
        using var publicationLock = AcquirePublicationLock(lockPath);
        if (!LedgerDirectoryMatches(directory, expectedBaselineFiles))
        {
            throw new InvalidOperationException(
                "accepted event files changed while ledger-append was replacing the snapshot");
        }

        ReapStaleStagingDirectories(directory);
        var planned = files.OrderBy(static file => file.Path.Value, StringComparer.Ordinal).ToImmutableArray();
        if (planned.Select(static file => file.Path).Distinct().Count() != planned.Length)
        {
            throw new InvalidOperationException("replacement frozen ledger contains duplicate paths");
        }

        var stagingDirectory = Path.Combine(directory, $".ledger-stage-{Guid.NewGuid():N}");
        var newDirectory = Path.Combine(stagingDirectory, "new");
        var oldDirectory = Path.Combine(stagingDirectory, "old");
        var published = new Stack<string>();
        var displaced = new Stack<(string Staged, string Original)>();
        try
        {
            Directory.CreateDirectory(newDirectory);
            Directory.CreateDirectory(oldDirectory);
            foreach (var file in planned)
            {
                var stagedPath = Path.Combine(newDirectory, Path.GetFileName(file.Path.Value));
                using var stream = new FileStream(
                    stagedPath,
                    FileMode.CreateNew,
                    FileAccess.Write,
                    FileShare.None);
                stream.Write(file.RawBytes.AsSpan());
                stream.Flush(flushToDisk: true);
            }

            foreach (var file in expectedBaselineFiles)
            {
                var original = Path.Combine(directory, Path.GetFileName(file.Path.Value));
                var staged = Path.Combine(oldDirectory, Path.GetFileName(file.Path.Value));
                File.Move(original, staged);
                displaced.Push((staged, original));
            }

            foreach (var file in planned)
            {
                var fileName = Path.GetFileName(file.Path.Value);
                var staged = Path.Combine(newDirectory, fileName);
                var final = Path.Combine(directory, fileName);
                File.Move(staged, final);
                published.Push(final);
            }

            Directory.Delete(stagingDirectory, recursive: true);
        }
        catch
        {
            RollbackCreatedFiles(published);
            while (displaced.TryPop(out var item))
            {
                if (File.Exists(item.Staged))
                {
                    File.Move(item.Staged, item.Original);
                }
            }

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
