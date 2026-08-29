using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    private const string ImplementationPath =
        "tools/StrataLint.Cli/Commands/Digestion/IngestCommand.cs";

    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier scribeEmissionVerifier,
        IReadOnlyList<string> arguments)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(scribeEmissionVerifier);
        ArgumentNullException.ThrowIfNull(arguments);
        try
        {
            var baselineRevision = ParseArguments(arguments);
            var prepared = Prepare(repository, baselineRevision);
            var currentRaw = prepared.CurrentRaw;
            var current = prepared.Current;
            var baseline = prepared.Baseline;
            var document = prepared.CurrentDocument;
            var baselineDocument = prepared.BaselineDocument;
            var plan = prepared.Plan;
            var repositoryChanges = prepared.RepositoryChanges;
            var plannedRaw = prepared.PlannedRaw;
            var plannedSnapshot = prepared.PlannedSnapshot;
            var plannedDocument = prepared.PlannedDocument;
            var plannedChanges = prepared.PlannedChanges;
            var plannedScope = prepared.PlannedScope;
            var report = leanReportSource.Load(current);
            var lean = ValidateLean(plannedSnapshot, report);
            var truthStates = LeanTruthStates.Resolve(plannedSnapshot, lean);
            var verifiedScribeEmissions = scribeEmissionVerifier.Verify(
                plannedSnapshot,
                report,
                plannedChanges);
            var derived = DigestionStatusEvaluator.Evaluate(
                plannedScope,
                plannedDocument,
                plannedSnapshot,
                lean,
                verifiedScribeEmissions,
                baselineDocument,
                validateProjectedStatus: false,
                baselineSnapshot: baseline,
                changes: plannedChanges,
                truthStates: truthStates);
            RequireNoReceiptIntegrityFailure(derived);

            var statusByAtomId = derived.Entries.ToDictionary(
                static item => item.Entry.AtomId,
                static item => item.DerivedStatus,
                StringComparer.Ordinal);
            var refreshed = plannedDocument.WithDigestionSources(
                plannedDocument.RequireDigestionSources()
                    .Select(source => source with
                    {
                        Entries = source.Entries
                            .Select(entry => entry with
                            {
                                ProjectedStatus = statusByAtomId[entry.AtomId],
                            })
                            .ToImmutableArray(),
                    })
                    .ToImmutableArray());
            var finalRaw = AddCasObjects(
                ReplaceLedger(currentRaw, document, refreshed),
                plan.CasObjects);
            var finalSnapshot = Decode(finalRaw);
            LeanTruthStates.RequireSameManagedInputs(plannedSnapshot, finalSnapshot);
            var finalDocument = LoadDocument(finalSnapshot);
            var finalChanges = IngestChanges(
                repositoryChanges,
                currentRaw,
                finalRaw,
                finalDocument,
                plan.CasObjects);
            var finalScope = DigestionEvaluationScopes.ForChanges(
                finalChanges,
                ImplementationPath);
            var evaluation = DigestionStatusEvaluator.Evaluate(
                finalScope,
                finalDocument,
                finalSnapshot,
                lean,
                verifiedScribeEmissions,
                baselineDocument,
                baselineSnapshot: baseline,
                changes: finalChanges,
                truthStates: truthStates);
            RequireNoReceiptIntegrityFailure(evaluation);
            var backfillObservations = DigestionBackfillValidation.RequireValidBackfill(
                finalDocument,
                finalSnapshot,
                baseline,
                LoadPolicy(finalSnapshot),
                lean,
                verifiedScribeEmissions,
                DigestionEvaluationScopes.ResolveChanges(finalScope, finalChanges));

            return WriteResult(
                repositoryRoot,
                prepared,
                finalRaw,
                finalDocument,
                evaluation,
                backfillObservations);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"INGEST_INVALID {exception.Message}\n");
        }
    }

    private static IngestPreparation Prepare(IRepositoryGateway repository, string baselineRevision)
    {
        var inputs = ReadInputs(repository, baselineRevision);
        return Prepare(repository, baselineRevision, inputs);
    }

    private static IngestInputs ReadInputs(
        IRepositoryGateway repository,
        string baselineRevision,
        bool requireBaselineSourceMetadata = false)
    {
        var currentRaw = repository.ReadCurrent();
        var baselineRaw = repository.ReadRevision(baselineRevision);
        var current = Decode(currentRaw);
        var baseline = Decode(baselineRaw);
        return new IngestInputs(
            currentRaw,
            current,
            baseline,
            LoadDocument(current),
            requireBaselineSourceMetadata
                ? BackfillInventoryLoader.Load(baseline)
                : BackfillInventoryLoader.LoadBaseline(baseline));
    }

    private static IngestPreparation Prepare(
        IRepositoryGateway repository,
        string baselineRevision,
        IngestInputs inputs) =>
        Prepare(
            repository,
            baselineRevision,
            inputs,
            repository.ReadChanges(baselineRevision));

    private static IngestPreparation Prepare(
        IRepositoryGateway repository,
        string baselineRevision,
        IngestInputs inputs,
        RawChangeSet repositoryChanges)
    {
        var currentRaw = inputs.CurrentRaw;
        var current = inputs.Current;
        var baseline = inputs.Baseline;
        var currentDocument = inputs.CurrentDocument;
        var baselineDocument = inputs.BaselineDocument;
        var plan = DigestionIngestor.Plan(
            currentDocument,
            current,
            baselineDocument,
            baseline);
        var plannedRaw = AddCasObjects(
            ReplaceLedger(currentRaw, currentDocument, plan.Document),
            plan.CasObjects);
        var plannedSnapshot = Decode(plannedRaw);
        var plannedDocument = LoadDocument(plannedSnapshot);
        var plannedChanges = IngestChanges(
            repositoryChanges,
            currentRaw,
            plannedRaw,
            plannedDocument,
            plan.CasObjects);
        var plannedScope = DigestionEvaluationScopes.ForChanges(
            plannedChanges,
            ImplementationPath);
        return new IngestPreparation(
            currentRaw,
            current,
            baseline,
            currentDocument,
            baselineDocument,
            plan,
            repositoryChanges,
            plannedRaw,
            plannedSnapshot,
            plannedDocument,
            plannedChanges,
            plannedScope,
            RenderCrossVolumeClearanceGaps(plan.Document, baselineDocument),
            SilentZeroExtractionWarnings(
                currentDocument,
                plan.Document,
                current,
                baseline));
    }

    private static ImmutableArray<DigestionLedgerSource> SilentZeroExtractionWarnings(
        BackfillInventoryDocument currentDocument,
        BackfillInventoryDocument plannedDocument,
        RepositorySnapshot current,
        RepositorySnapshot baseline)
    {
        var plannedSources = plannedDocument.RequireDigestionSources()
            .ToDictionary(static source => source.SourceId, StringComparer.Ordinal);
        return currentDocument.RequireDigestionSources()
            .Where(source => AtomizerRegistry.IsRegistered(source.Atomizer))
            .Where(source => current.TryGetFile(source.SourcePath, out var currentFile)
                && baseline.TryGetFile(source.SourcePath, out var baselineFile)
                && !currentFile.RawBytes.AsSpan().SequenceEqual(baselineFile.RawBytes.AsSpan()))
            .Where(source => plannedSources[source.SourceId].Entries.Length == source.Entries.Length)
            .OrderBy(static source => source.SourceId, StringComparer.Ordinal)
            .ToImmutableArray();
    }

    private static string RenderCrossVolumeClearanceGaps(
        BackfillInventoryDocument currentDocument,
        BackfillInventoryDocument baselineDocument)
    {
        var currentHosts = ResidualHosts(currentDocument)
            .Distinct()
            .ToArray();
        var currentVotes = currentHosts
            .Select(static host => new ResidueSourceVote(host.Residue, host.SourceId))
            .ToHashSet();
        var currentByName = currentHosts.ToLookup(static host => host.Residue, StringComparer.Ordinal);
        var cleared = ResidualHosts(baselineDocument)
            .GroupBy(static host => new ResidueSourceVote(host.Residue, host.SourceId))
            .Where(group => !currentVotes.Contains(group.Key))
            .Select(static group => group
                .OrderBy(static host => host.AtomId, StringComparer.Ordinal)
                .First())
            .OrderBy(static host => host.Residue, StringComparer.Ordinal)
            .ThenBy(static host => host.SourceId, StringComparer.Ordinal)
            .ThenBy(static host => host.AtomId, StringComparer.Ordinal);
        var writer = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        foreach (var host in cleared)
        {
            var hangingHosts = currentByName[host.Residue]
                .Where(candidate => !string.Equals(
                    candidate.SourceId,
                    host.SourceId,
                    StringComparison.Ordinal))
                .OrderBy(static candidate => candidate.SourceId, StringComparer.Ordinal)
                .ThenBy(static candidate => candidate.AtomId, StringComparer.Ordinal)
                .Select(static candidate => $"{candidate.SourceId}/{candidate.AtomId}")
                .ToArray();
            if (hangingHosts.Length == 0)
            {
                continue;
            }

            var detail = JsonSerializer.Serialize(new
            {
                residue = host.Residue,
                cleared_source = host.SourceId,
                hanging_hosts = hangingHosts,
            });
            writer.WriteLine(
                $"GAP atom={host.AtomId} code=cross-volume-shared-residue-half-cleared "
                + $"severity=warn detail={detail}");
        }

        return writer.ToString();
    }

    private static IEnumerable<ResidualHost> ResidualHosts(BackfillInventoryDocument document) =>
        document.RequireDigestionEntries().SelectMany(static entry =>
            entry.Receipts.UnresolvedSubitems.Select(residue =>
                new ResidualHost(residue, entry.SourceId, entry.AtomId)));

    private sealed record ResidualHost(string Residue, string SourceId, string AtomId);

    private sealed record ResidueSourceVote(string Residue, string SourceId);

    private static string ParseArguments(IReadOnlyList<string> arguments)
    {
        if (arguments.Count == 2
            && arguments[0] == "--base"
            && !string.IsNullOrWhiteSpace(arguments[1]))
        {
            return arguments[1];
        }

        throw new InvalidOperationException("USAGE: StrataLint ingest --base REV");
    }

    private static BackfillInventoryDocument LoadDocument(RepositorySnapshot snapshot) =>
        BackfillInventoryLoader.Load(snapshot);

    internal static RawRepositorySnapshot ReplaceLedger(
        RawRepositorySnapshot snapshot,
        BackfillInventoryDocument current,
        BackfillInventoryDocument replacement)
    {
        var matches = snapshot.Entries.Count(static entry =>
            entry.Path == BackfillInventoryLoader.RelativePath);
        if (matches > 0)
        {
            throw new InvalidOperationException("ingest does not write legacy digestion ledgers");
        }

        var entries = snapshot.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        var currentSources = current.RequireDigestionSources().ToDictionary(
            static source => source.SourceId,
            StringComparer.Ordinal);
        var replacementSources = replacement.RequireDigestionSources().ToDictionary(
            static source => source.SourceId,
            StringComparer.Ordinal);
        // Adding is how a theory document nobody declared enters the ledger, so it is
        // allowed and writes the source metadata below. Removing is not: a source that
        // disappears would take its receipts with it, which is the one direction the
        // append-only ledger does not have.
        var removed = currentSources.Keys.Except(replacementSources.Keys, StringComparer.Ordinal).ToArray();
        if (removed.Length > 0)
        {
            throw new InvalidOperationException(
                "ingest cannot remove directory ledger sources: "
                + string.Join(", ", removed.Order(StringComparer.Ordinal)));
        }

        foreach (var (sourceId, replacementSource) in replacementSources)
        {
            if (currentSources.TryGetValue(sourceId, out var currentSource)
                && SourceMetadataEquals(currentSource, replacementSource))
            {
                continue;
            }

            var metadataPath = $"{BackfillInventoryLoader.RootPath}{sourceId}/source.toml";
            entries[metadataPath] = new RawRepositoryEntry(
                metadataPath,
                BackfillInventoryWriter.WriteSourceMetadata(replacementSource));
        }

        var currentEntries = current.RequireDigestionEntries().ToDictionary(
            static entry => (entry.SourceId, entry.AtomId));
        var replacementEntries = replacement.RequireDigestionEntries().ToDictionary(
            static entry => (entry.SourceId, entry.AtomId));
        foreach (var key in currentEntries.Keys.Except(replacementEntries.Keys))
        {
            throw new InvalidOperationException(
                $"ingest cannot remove directory ledger atom {key.AtomId}");
        }

        foreach (var (key, replacementEntry) in replacementEntries)
        {
            if (currentEntries.TryGetValue(key, out var currentEntry))
            {
                var currentBytes = BackfillInventoryWriter.WriteAtom(currentEntry);
                var replacementBytes = BackfillInventoryWriter.WriteAtom(replacementEntry);
                var currentPath = ExistingAtomPath(entries.Keys, key.SourceId, key.AtomId);
                var replacementPath = NewAtomPath(replacementEntry);
                if (currentPath == replacementPath
                    && currentBytes.AsSpan().SequenceEqual(replacementBytes.AsSpan()))
                {
                    continue;
                }

                entries.Remove(currentPath);
                if (!entries.TryAdd(
                        replacementPath,
                        new RawRepositoryEntry(replacementPath, replacementBytes)))
                {
                    throw new InvalidOperationException(
                        $"directory ledger atom path already exists: {replacementPath}");
                }

                continue;
            }

            var path = NewAtomPath(replacementEntry);
            if (!entries.TryAdd(
                    path,
                    new RawRepositoryEntry(path, BackfillInventoryWriter.WriteAtom(replacementEntry))))
            {
                throw new InvalidOperationException($"directory ledger atom path already exists: {path}");
            }
        }

        return RawRepositorySnapshot.Create(entries.Values.OrderBy(
            static entry => entry.Path,
            StringComparer.Ordinal));
    }

    private static bool SourceMetadataEquals(
        DigestionLedgerSource current,
        DigestionLedgerSource replacement) =>
        string.Equals(current.SourcePath, replacement.SourcePath, StringComparison.Ordinal)
        && string.Equals(current.Atomizer, replacement.Atomizer, StringComparison.Ordinal)
        && current.GenreRegistryCheck.Kind == replacement.GenreRegistryCheck.Kind
        && current.GenreRegistryCheck.UnregisteredGenres.SequenceEqual(
            replacement.GenreRegistryCheck.UnregisteredGenres,
            StringComparer.Ordinal)
        && current.AcknowledgedStale.SequenceEqual(replacement.AcknowledgedStale);

    private static string ExistingAtomPath(
        IEnumerable<string> paths,
        string sourceId,
        string atomId)
    {
        var sourceRoot = $"{BackfillInventoryLoader.RootPath}{sourceId}/";
        var suffix = $"/{atomId}.yaml";
        var matches = paths.Where(path =>
                path.StartsWith(sourceRoot, StringComparison.Ordinal)
                && path.EndsWith(suffix, StringComparison.Ordinal))
            .ToArray();
        return matches.Length == 1
            ? matches[0]
            : throw new InvalidOperationException(
                $"directory ledger atom {sourceId}/{atomId} does not have exactly one canonical path");
    }

    internal static void ApplyLedgerUpdatesAtomically(
        string repositoryRoot,
        RawRepositorySnapshot current,
        ImmutableArray<LedgerUpdate> updates,
        Action<string, string>? commit = null)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(current);
        if (updates.Length == 0)
        {
            return;
        }

        var root = Path.GetFullPath(repositoryRoot);
        var expected = current.Entries
            .Where(static entry => IsLedgerPath(entry.Path))
            .ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        var actual = ReadLedgerFiles(root);
        if (expected.Keys.Except(actual.Keys, StringComparer.Ordinal).Any())
        {
            throw new InvalidOperationException(
                "ledger went missing between read and write; aborting to avoid a lost update");
        }

        if (actual.Keys.Except(expected.Keys, StringComparer.Ordinal).Any()
            || expected.Any(pair => !pair.Value.Bytes.AsSpan().SequenceEqual(
                actual[pair.Key].AsSpan())))
        {
            throw new InvalidOperationException(
                "ledger changed under us between read and write; aborting to avoid a lost update");
        }

        var originals = updates.ToDictionary(
            static update => update.Path,
            update => actual.TryGetValue(update.Path, out var bytes)
                ? (ImmutableArray<byte>?)bytes
                : null,
            StringComparer.Ordinal);
        var touched = new List<string>(updates.Length);
        try
        {
            foreach (var update in updates
                         .OrderBy(static update => update.DurabilityOrder)
                         .ThenBy(static update => update.Path, StringComparer.Ordinal))
            {
                touched.Add(update.Path);
                var outputPath = Path.Combine(
                    root,
                    update.Path.Replace('/', Path.DirectorySeparatorChar));
                if (update.Bytes is null)
                {
                    File.Delete(outputPath);
                    continue;
                }

                Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
                ReplaceLedgerAtomically(outputPath, update.Bytes.Value.AsSpan(), commit);
            }

            PruneEmptyLedgerDirectories(root, updates);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            RollbackLedgerUpdates(root, touched, originals, exception);
            throw;
        }
    }

    private static bool IsLedgerPath(string path) =>
        string.Equals(path, BackfillInventoryLoader.RelativePath, StringComparison.Ordinal)
        || BackfillInventoryLoader.IsCanonicalPath(path);

    private static Dictionary<string, ImmutableArray<byte>> ReadLedgerFiles(string root)
    {
        var result = new Dictionary<string, ImmutableArray<byte>>(StringComparer.Ordinal);
        AddIfFile(BackfillInventoryLoader.RelativePath);
        var directory = Path.Combine(
            root,
            BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar));
        if (Directory.Exists(directory))
        {
            foreach (var path in Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories))
            {
                Add(Path.GetRelativePath(root, path).Replace(Path.DirectorySeparatorChar, '/'), path);
            }
        }

        return result;

        void AddIfFile(string relativePath)
        {
            var fullPath = Path.Combine(
                root,
                relativePath.Replace('/', Path.DirectorySeparatorChar));
            if (File.Exists(fullPath))
            {
                Add(relativePath, fullPath);
            }
        }

        void Add(string relativePath, string fullPath) =>
            result.Add(relativePath, ImmutableArray.CreateRange(File.ReadAllBytes(fullPath)));
    }

    private static void PruneEmptyLedgerDirectories(
        string root,
        IEnumerable<LedgerUpdate> updates)
    {
        var ledgerRoot = Path.GetFullPath(Path.Combine(
            root,
            BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar)));
        var ledgerRootPrefix = ledgerRoot.EndsWith(Path.DirectorySeparatorChar)
            ? ledgerRoot
            : ledgerRoot + Path.DirectorySeparatorChar;
        var directories = new HashSet<string>(StringComparer.Ordinal);
        foreach (var update in updates.Where(static update =>
                     update.Bytes is null
                     && update.Path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal)
                     && BackfillInventoryLoader.IsCanonicalPath(update.Path)))
        {
            var outputPath = Path.GetFullPath(Path.Combine(
                root,
                update.Path.Replace('/', Path.DirectorySeparatorChar)));
            for (var directory = Path.GetDirectoryName(outputPath);
                 directory is not null
                 && directory.StartsWith(ledgerRootPrefix, StringComparison.Ordinal);
                 directory = Path.GetDirectoryName(directory))
            {
                directories.Add(directory);
            }
        }

        foreach (var directory in directories
                     .OrderByDescending(static path => path.Length)
                     .ThenBy(static path => path, StringComparer.Ordinal))
        {
            if (Directory.Exists(directory)
                && !Directory.EnumerateFileSystemEntries(directory).Any())
            {
                Directory.Delete(directory);
            }
        }
    }

    private static void RollbackLedgerUpdates(
        string root,
        IEnumerable<string> touched,
        IReadOnlyDictionary<string, ImmutableArray<byte>?> originals,
        Exception writeFailure)
    {
        var rollbackFailures = new List<Exception>();
        foreach (var path in touched.Reverse())
        {
            var outputPath = Path.Combine(
                root,
                path.Replace('/', Path.DirectorySeparatorChar));
            try
            {
                if (originals[path] is { } bytes)
                {
                    Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
                    ReplaceLedgerAtomically(outputPath, bytes.AsSpan());
                }
                else
                {
                    File.Delete(outputPath);
                }
            }
            catch (Exception exception) when (exception is not OutOfMemoryException)
            {
                rollbackFailures.Add(exception);
            }
        }

        if (rollbackFailures.Count > 0)
        {
            throw new AggregateException(
                "ledger write failed and rollback was incomplete",
                new[] { writeFailure }.Concat(rollbackFailures));
        }
    }

    private static RawRepositorySnapshot AddCasObjects(
        RawRepositorySnapshot snapshot,
        ImmutableArray<DigestionCasObject> casObjects)
    {
        var entries = snapshot.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        foreach (var item in casObjects)
        {
            if (entries.TryGetValue(item.RelativePath, out var existing))
            {
                if (!existing.Bytes.AsSpan().SequenceEqual(item.Bytes.AsSpan()))
                {
                    throw new InvalidOperationException(
                        $"CAS path already contains different bytes: {item.RelativePath}");
                }

                continue;
            }

            entries.Add(item.RelativePath, new RawRepositoryEntry(item.RelativePath, item.Bytes));
        }

        return RawRepositorySnapshot.Create(entries.Values.OrderBy(
            static entry => entry.Path,
            StringComparer.Ordinal));
    }

    private static ImmutableArray<string> WriteCasObjects(
        string repositoryRoot,
        ImmutableArray<DigestionCasObject> casObjects)
    {
        var pending = new List<(DigestionCasObject Object, string FullPath)>();
        var root = Path.GetFullPath(repositoryRoot);
        foreach (var item in casObjects)
        {
            var fullPath = Path.Combine(
                root,
                item.RelativePath.Replace('/', Path.DirectorySeparatorChar));
            if (File.Exists(fullPath))
            {
                if (!File.ReadAllBytes(fullPath).AsSpan().SequenceEqual(item.Bytes.AsSpan()))
                {
                    throw new InvalidOperationException(
                        $"CAS path already contains different bytes: {item.RelativePath}");
                }

                continue;
            }

            pending.Add((item, fullPath));
        }

        var created = ImmutableArray.CreateBuilder<string>(pending.Count);
        try
        {
            foreach (var (item, fullPath) in pending)
            {
                Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
                using var output = new FileStream(
                    fullPath,
                    FileMode.CreateNew,
                    FileAccess.Write,
                    FileShare.None);
                created.Add(fullPath);
                output.Write(item.Bytes.AsSpan());
                output.Flush(flushToDisk: true);
            }
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            RollbackCasObjects(created, exception);
            throw;
        }

        return created.ToImmutable();
    }

    internal static void ReplaceLedgerAtomically(
        string outputPath,
        ReadOnlySpan<byte> bytes,
        Action<string, string>? commit = null)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(outputPath);
        var target = Path.GetFullPath(outputPath);
        var directory = Path.GetDirectoryName(target)
            ?? throw new InvalidOperationException("ledger output path has no parent directory");
        var pending = Path.Combine(
            directory,
            $".{Path.GetFileName(target)}.{Guid.NewGuid():N}.tmp");
        try
        {
            using (var output = new FileStream(
                       pending,
                       FileMode.CreateNew,
                       FileAccess.Write,
                       FileShare.None))
            {
                output.Write(bytes);
                output.Flush(flushToDisk: true);
            }

            commit ??= static (source, destination) =>
                File.Move(source, destination, overwrite: true);
            commit(pending, target);
        }
        finally
        {
            File.Delete(pending);
        }
    }

    private static void RollbackCasObjects(
        IEnumerable<string> createdPaths,
        Exception writeFailure)
    {
        var rollbackFailures = new List<Exception>();
        foreach (var path in createdPaths.Reverse())
        {
            try
            {
                File.Delete(path);
            }
            catch (Exception exception) when (exception is not OutOfMemoryException)
            {
                rollbackFailures.Add(exception);
            }
        }

        if (rollbackFailures.Count > 0)
        {
            throw new AggregateException(
                "CAS write failed and rollback was incomplete",
                new[] { writeFailure }.Concat(rollbackFailures));
        }
    }

    private static ValidatedPolicy LoadPolicy(RepositorySnapshot snapshot)
    {
        if (!snapshot.TryGetFile("Meta/registry.yaml", out var registry)
            || !snapshot.TryGetFile("Meta/domains.yaml", out var domains))
        {
            throw new InvalidOperationException(
                "ingest requires Meta/registry.yaml and Meta/domains.yaml");
        }

        return RegistryLoader.Load(registry.RawBytes.AsSpan(), domains.RawBytes.AsSpan()) switch
        {
            RegistryLoadOutcome.Accepted accepted => accepted.Policy,
            RegistryLoadOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private static AcceptedLeanClosure ValidateLean(
        RepositorySnapshot snapshot,
        LeanAxiomReport report) =>
        LeanClosureValidator.Validate(snapshot, report) switch
        {
            LeanValidationOutcome.Accepted accepted => accepted.Capability,
            LeanValidationOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    internal static void RequireNoReceiptIntegrityFailure(
        DigestionLedgerEvaluation evaluation)
    {
        if (evaluation.HasReceiptIntegrityFailure)
        {
            throw new InvalidOperationException(
                "digest status is invalid: "
                + string.Join("; ", evaluation.ReceiptIntegrityFailureReasons));
        }
    }
}
