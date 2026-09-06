using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal sealed record ReportFreeDigestionIngestPlan(
    BackfillInventoryDocument Document,
    int ResidualOpenAdded,
    int SkippedExisting,
    ImmutableArray<DigestionCasObject> CasObjects,
    ImmutableArray<DigestionIngestFallback> Fallbacks,
    ImmutableHashSet<string> AddedAtomIds);

internal static class ReportFreeDigestionIngestor
{
    private static readonly DigestionStatus ResidualOpen = new(
        DigestionMigrationState.Residual,
        DigestionTruthState.Open);

    internal static ReportFreeDigestionIngestPlan Plan(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        BackfillInventoryDocument baselineDocument,
        ImmutableHashSet<string>? sourceIds = null,
        ImmutableHashSet<string>? registrationPaths = null,
        Func<string, TheoryAtomizer>? atomizerResolver = null,
        Func<string, TheoryAtomizerWithContentKinds>? contentKindAtomizerResolver = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(baselineDocument);
        if (atomizerResolver is null && contentKindAtomizerResolver is null)
        {
            contentKindAtomizerResolver = static id =>
                AtomizerRegistry.Require(id).AtomizeWithContentKinds;
        }
        atomizerResolver ??= static id => AtomizerRegistry.Require(id).Atomize;

        var currentAtomIds = document.RequireDigestionEntries()
            .Select(static entry => entry.AtomId)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var reservedRemovedAtomIds = baselineDocument.RequireDigestionEntries()
            .Select(static entry => entry.AtomId)
            .Except(currentAtomIds, StringComparer.Ordinal)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var currentSourceIds = document.RequireDigestionSources()
            .Select(static source => source.SourceId)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var migrationDocument = DigestionIngestor.RegisterDefaultTheorySources(
            document,
            snapshot,
            sourceIds is null ? null : registrationPaths ?? ImmutableHashSet<string>.Empty);

        var selectedSources = migrationDocument.RequireDigestionSources()
            .Where(source => sourceIds is null || sourceIds.Contains(source.SourceId))
            .ToArray();
        foreach (var source in selectedSources)
        {
            if (snapshot.TryGetFile(source.SourcePath, out var sourceFile)
                && DigestionSourceConflictMarkers.FindFirstLine(sourceFile.RawBytes.AsSpan()) is { } line)
            {
                throw new FormatException(
                    DigestionSourceConflictMarkers.FormatFinding(source.SourcePath, line));
            }
        }

        if (!TheoryAtomizerDataLoader.TryLoad(snapshot, out var atomizerRules))
        {
            throw new FormatException(
                $"Atomizer data file is missing: {TheoryAtomizerDataLoader.DataPath}");
        }

        var knownAtomIds = currentAtomIds.ToHashSet(StringComparer.Ordinal);
        var casObjects = new Dictionary<string, DigestionCasObject>(StringComparer.Ordinal);
        var addedAtomIds = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var fallbacks = ImmutableArray.CreateBuilder<DigestionIngestFallback>();
        var sources = ImmutableArray.CreateBuilder<DigestionLedgerSource>();
        var residualOpenAdded = 0;
        var skippedExisting = 0;

        foreach (var source in migrationDocument.RequireDigestionSources())
        {
            if (sourceIds is not null && !sourceIds.Contains(source.SourceId))
            {
                sources.Add(source);
                continue;
            }

            if (!AtomizerRegistry.IsRegistered(source.Atomizer))
            {
                if (source.Atomizer != AtomizerRegistry.NoAtomizerId)
                {
                    throw new FormatException(
                        $"ingest source {source.SourceId} has unknown atomizer {source.Atomizer}");
                }

                sources.Add(source);
                continue;
            }

            if (!snapshot.TryGetFile(source.SourcePath, out var sourceFile))
            {
                throw new FormatException($"source path is dangling: {source.SourcePath}");
            }

            var atomized = Atomize(
                source,
                sourceFile.RawBytes,
                atomizerRules,
                atomizerResolver,
                contentKindAtomizerResolver,
                currentAtomIds,
                fallbacks);
            var outputSource = currentSourceIds.Contains(source.SourceId)
                ? source
                : source with
                {
                    GenreRegistryProjection =
                        GenreRegistryProjection.Available(atomized.GenreRegistryCheck),
                };
            var entries = outputSource.Entries.ToBuilder();
            var newIndexes = new Dictionary<string, int>(StringComparer.Ordinal);

            foreach (var atom in atomized.Claims
                         .GroupBy(static atom => atom.Fingerprints.RawSha256, StringComparer.Ordinal)
                         .Select(static group => group.First()))
            {
                var atomId = AtomId(atom);
                if (currentAtomIds.Contains(atomId))
                {
                    skippedExisting++;
                    continue;
                }
                if (reservedRemovedAtomIds.Contains(atomId) || !knownAtomIds.Add(atomId))
                {
                    continue;
                }

                var captured = AddCasObject(atom.RawBytes.AsSpan(), casObjects);
                var entry = NewEntry(outputSource, atom, atomId, captured.Reference);
                newIndexes.Add(atomId, entries.Count);
                entries.Add(entry);
                addedAtomIds.Add(atomId);
                residualOpenAdded++;
            }

            foreach (var clausePlan in atomized.ClausePlans
                         .GroupBy(static plan => plan.Parent.Fingerprints.RawSha256, StringComparer.Ordinal)
                         .Select(static group => group.First()))
            {
                var parentId = AtomId(clausePlan.Parent);
                if (!newIndexes.TryGetValue(parentId, out var parentIndex))
                {
                    continue;
                }

                var childObjects = clausePlan.Children
                    .Select(child => (Atom: child, Captured: DigestionCasStore.Capture(child.RawBytes.AsSpan())))
                    .ToArray();
                if (childObjects.Any(item =>
                        reservedRemovedAtomIds.Contains(item.Captured.Reference["sha256:".Length..])
                        && !knownAtomIds.Contains(item.Captured.Reference["sha256:".Length..])))
                {
                    continue;
                }

                var chain = ImmutableArray.CreateBuilder<string>(childObjects.Length);
                foreach (var (child, captured) in childObjects)
                {
                    var childId = captured.Reference["sha256:".Length..];
                    chain.Add(childId);
                    if (currentAtomIds.Contains(childId))
                    {
                        skippedExisting++;
                        continue;
                    }
                    if (!knownAtomIds.Add(childId))
                    {
                        continue;
                    }

                    AddCasObject(child.RawBytes.AsSpan(), casObjects);
                    newIndexes.Add(childId, entries.Count);
                    entries.Add(NewEntry(outputSource, child, childId, captured.Reference));
                    addedAtomIds.Add(childId);
                    residualOpenAdded++;
                }

                var parent = entries[parentIndex];
                entries[parentIndex] = parent with
                {
                    Receipts = parent.Receipts with
                    {
                        ChainAtoms = chain.MoveToImmutable(),
                        UnresolvedSubitems = [],
                    },
                };
            }

            sources.Add(outputSource with { Entries = entries.ToImmutable() });
        }

        return new ReportFreeDigestionIngestPlan(
            migrationDocument.WithDigestionSources(sources.ToImmutable()),
            residualOpenAdded,
            skippedExisting,
            casObjects.Values
                .OrderBy(static item => item.RelativePath, StringComparer.Ordinal)
                .ToImmutableArray(),
            fallbacks.ToImmutable(),
            addedAtomIds.ToImmutable());
    }

    private static AtomizedTheoryDocument Atomize(
        DigestionLedgerSource source,
        ImmutableArray<byte> sourceBytes,
        TheoryAtomizerRules rules,
        Func<string, TheoryAtomizer> atomizerResolver,
        Func<string, TheoryAtomizerWithContentKinds>? contentKindAtomizerResolver,
        ImmutableHashSet<string> currentAtomIds,
        ImmutableArray<DigestionIngestFallback>.Builder fallbacks)
    {
        AtomizedTheoryDocument atomized;
        try
        {
            atomized = contentKindAtomizerResolver is null
                ? atomizerResolver(source.Atomizer)(sourceBytes.AsSpan(), rules)
                : contentKindAtomizerResolver(source.Atomizer)(
                    sourceBytes.AsSpan(),
                    rules,
                    new Dictionary<string, string>(StringComparer.Ordinal));
        }
        catch (Exception exception) when (
            exception is TheorySourceFormatException or DecoderFallbackException)
        {
            return CoarseFallback(source, sourceBytes, exception.Message, currentAtomIds, fallbacks);
        }

        if (DigestionLedgerAligner.AtomizerIntegrityFailure(
                atomized,
                sourceBytes.AsSpan()) is { } integrityFailure)
        {
            throw new FormatException(
                $"source {source.SourceId} atomizer integrity failed: {integrityFailure}");
        }
        if (!atomized.Claims.IsEmpty)
        {
            return atomized;
        }

        return CoarseFallback(
            source,
            sourceBytes,
            "atomizer recognition is incomplete or empty",
            currentAtomIds,
            fallbacks);
    }

    private static AtomizedTheoryDocument CoarseFallback(
        DigestionLedgerSource source,
        ImmutableArray<byte> sourceBytes,
        string reason,
        ImmutableHashSet<string> currentAtomIds,
        ImmutableArray<DigestionIngestFallback>.Builder fallbacks)
    {
        var fingerprints = DigestionFingerprint.ComputeOpaque(sourceBytes.AsSpan());
        var atomId = fingerprints.RawSha256["sha256:".Length..];
        if (!source.Entries.IsEmpty
            && !source.Entries.Any(entry => entry.AtomId == atomId)
            && !currentAtomIds.Contains(atomId))
        {
            throw new FormatException($"source {source.SourceId} atomization failed: {reason}");
        }

        fallbacks.Add(new DigestionIngestFallback(source.SourceId, reason));
        var atom = new DigestionAtom(
            0,
            sourceBytes.Length,
            sourceBytes,
            fingerprints,
            []);
        return new AtomizedTheoryDocument(
            [atom],
            [new DigestionSlice(true, sourceBytes)],
            source.GenreRegistryCheck);
    }

    private static DigestionLedgerEntry NewEntry(
        DigestionLedgerSource source,
        DigestionAtom atom,
        string atomId,
        string casReference) =>
        new(
            source.SourceId,
            source.SourcePath,
            source.Atomizer,
            atomId,
            atom.Fingerprints,
            [],
            new DigestionReceipts([], [], [], null),
            ResidualOpen,
            casReference);

    private static string AtomId(DigestionAtom atom)
    {
        if (!DigestionFingerprint.IsCanonicalSha256(atom.Fingerprints.RawSha256))
        {
            throw new FormatException(
                $"ingest atom raw fingerprint is not canonical sha256: {atom.Fingerprints.RawSha256}");
        }

        return atom.Fingerprints.RawSha256["sha256:".Length..];
    }

    private static DigestionCasObject AddCasObject(
        ReadOnlySpan<byte> bytes,
        IDictionary<string, DigestionCasObject> casObjects)
    {
        var captured = DigestionCasStore.Capture(bytes);
        if (casObjects.TryGetValue(captured.Reference, out var existing))
        {
            if (!existing.Bytes.AsSpan().SequenceEqual(captured.Bytes.AsSpan()))
            {
                throw new FormatException($"ingest CAS collision at {captured.Reference}");
            }
            return existing;
        }

        casObjects.Add(captured.Reference, captured);
        return captured;
    }
}
