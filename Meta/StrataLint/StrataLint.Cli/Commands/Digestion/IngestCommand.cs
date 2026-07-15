using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class IngestCommand
{
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
            var currentRaw = repository.ReadCurrent();
            var baselineRaw = repository.ReadRevision(baselineRevision);
            var current = Decode(currentRaw);
            var baseline = Decode(baselineRaw);
            var document = LoadDocument(current, "candidate");
            var baselineDocument = LoadDocument(baseline, "baseline");
            var plan = DigestionIngestor.Plan(document, current, baselineDocument);
            var plannedBytes = BackfillInventoryWriter.WriteForIngest(plan.Document);
            var plannedRaw = AddCasObjects(
                ReplaceLedger(currentRaw, plannedBytes),
                plan.CasObjects);
            var plannedSnapshot = Decode(plannedRaw);
            var plannedDocument = LoadDocument(plannedSnapshot, "planned");
            var report = leanReportSource.Load(current);
            var lean = ValidateLean(plannedSnapshot, report);
            var verifiedScribeEmissions = scribeEmissionVerifier.Verify(report);
            var derived = DigestionStatusEvaluator.Evaluate(
                plannedDocument,
                plannedSnapshot,
                lean,
                verifiedScribeEmissions,
                baselineDocument,
                validateProjectedStatus: false);
            RequireNoFindings(derived);

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
            var finalBytes = BackfillInventoryWriter.WriteForIngest(refreshed);
            var finalRaw = AddCasObjects(
                ReplaceLedger(currentRaw, finalBytes),
                plan.CasObjects);
            var finalSnapshot = Decode(finalRaw);
            var finalDocument = LoadDocument(finalSnapshot, "final");
            var evaluation = DigestionStatusEvaluator.Evaluate(
                finalDocument,
                finalSnapshot,
                lean,
                verifiedScribeEmissions,
                baselineDocument);
            RequireNoFindings(evaluation);
            RequireValidBackfill(
                finalDocument,
                finalSnapshot,
                baseline,
                LoadPolicy(finalSnapshot),
                lean,
                verifiedScribeEmissions);

            var currentLedger = currentRaw.Entries.Single(static entry =>
                entry.Path == BackfillInventoryLoader.RelativePath);
            var changed = !currentLedger.Bytes.AsSpan().SequenceEqual(finalBytes.AsSpan());
            var createdCasPaths = WriteCasObjects(repositoryRoot, plan.CasObjects);
            try
            {
                if (changed)
                {
                    var outputPath = Path.Combine(
                        Path.GetFullPath(repositoryRoot),
                        BackfillInventoryLoader.RelativePath.Replace('/', Path.DirectorySeparatorChar));
                    ReplaceLedgerAtomically(outputPath, finalBytes.AsSpan());
                }
            }
            catch (Exception exception) when (exception is not OutOfMemoryException)
            {
                RollbackCasObjects(createdCasPaths, exception);
                throw;
            }

            return new CommandResult(
                true,
                $"INGEST stale_acknowledged={plan.StaleAcknowledged} "
                + $"residual_open_added={plan.ResidualOpenAdded} "
                + $"coarse_fallbacks={plan.Fallbacks.Length} "
                + $"cas_objects_written={createdCasPaths.Length} "
                + $"ledger_changed={changed.ToString().ToLowerInvariant()}\n"
                + string.Concat(plan.Fallbacks.Select(static fallback =>
                    $"INGEST_FALLBACK source={fallback.SourceId} reason={fallback.Reason}\n"))
                + DigestStatusCommand.RenderText(evaluation),
                string.Empty);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"INGEST_INVALID {exception.Message}\n");
        }
    }

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

    private static BackfillInventoryDocument LoadDocument(
        RepositorySnapshot snapshot,
        string side)
    {
        if (!snapshot.TryGetFile(BackfillInventoryLoader.RelativePath, out var file))
        {
            throw new InvalidOperationException(
                $"{side} {BackfillInventoryLoader.RelativePath} is missing");
        }

        return BackfillInventoryLoader.Load(file.Text);
    }

    private static RawRepositorySnapshot ReplaceLedger(
        RawRepositorySnapshot snapshot,
        ImmutableArray<byte> bytes)
    {
        var matches = snapshot.Entries.Count(static entry =>
            entry.Path == BackfillInventoryLoader.RelativePath);
        if (matches != 1)
        {
            throw new InvalidOperationException(
                $"snapshot must contain exactly one {BackfillInventoryLoader.RelativePath}");
        }

        return RawRepositorySnapshot.Create(snapshot.Entries.Select(entry =>
            entry.Path == BackfillInventoryLoader.RelativePath
                ? new RawRepositoryEntry(entry.Path, bytes)
                : entry));
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

    private static void RequireNoFindings(DigestionLedgerEvaluation evaluation)
    {
        if (evaluation.Findings.Length > 0)
        {
            throw new InvalidOperationException(
                "digest status is invalid: " + string.Join("; ", evaluation.Findings));
        }
    }

    private static void RequireValidBackfill(
        BackfillInventoryDocument document,
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        VerifiedScribeEmissions verifiedScribeEmissions)
    {
        var findings = BackfillInventoryRule.EvaluateDocument(
            new BackfillInventoryValidationContext(
                current,
                baseline,
                policy,
                lean,
                verifiedScribeEmissions),
            document);
        if (findings.Length > 0)
        {
            throw new InvalidOperationException(
                "SL-016 final ledger is invalid: "
                + string.Join("; ", findings.Select(static finding => finding.Message)));
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
}
