using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class DigestionIngestor
{
    internal static RawChangeSet IncludeCasReverseDependencies(
        BackfillInventoryDocument baselineDocument,
        RawChangeSet changes)
    {
        var entries = changes.Entries
            .Select(static change => (change.Path.Value, change.Kind))
            .ToList();
        var paths = changes.Paths
            .Select(static path => path.Value)
            .ToHashSet(StringComparer.Ordinal);
        var affectedCasPaths = baselineDocument.RequireDigestionEntries()
            .Where(entry => DigestionCasStore.EntryChanged(entry, changes))
            .Select(static entry => entry.CasRef)
            .Where(DigestionFingerprint.IsCanonicalSha256)
            .Select(static reference =>
                DigestionCasStore.RootPath + reference["sha256:".Length..])
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal);
        foreach (var path in affectedCasPaths)
        {
            if (paths.Add(path))
            {
                entries.Add((path, RawChangeKind.Modified));
            }
        }

        return RawChangeSet.CreateWithKinds(entries);
    }

    internal static DigestionIngestPlan Plan(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        BackfillInventoryDocument baselineDocument,
        RepositorySnapshot? baselineSnapshot = null,
        Func<string, TheoryAtomizer>? atomizerResolver = null,
        RawChangeSet? changes = null,
        ImmutableHashSet<string>? sourceIds = null,
        ImmutableHashSet<string>? registrationPaths = null,
        Func<string, TheoryAtomizerWithContentKinds>? contentKindAtomizerResolver = null,
        DigestionIngestStrategy strategy = DigestionIngestStrategy.Align)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(baselineDocument);

        var existingAtomIds = document.RequireDigestionEntries()
            .Select(static entry => entry.AtomId)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var reservedRemovedAtomIds = baselineDocument.RequireDigestionEntries()
            .Select(static entry => entry.AtomId)
            .Except(existingAtomIds, StringComparer.Ordinal)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var existingSourceIds = document.RequireDigestionSources()
            .Select(static source => source.SourceId)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var observations = new HashSet<DigestionIngestObservation>();
        void Observe(string atomId, string observedSourceId, string kind) =>
            observations.Add(new DigestionIngestObservation(atomId, observedSourceId, kind));

        var migrationDocument = RegisterDefaultTheorySources(document, snapshot,
            sourceIds is null ? null : registrationPaths ?? ImmutableHashSet<string>.Empty);
        var evaluationChanges = changes is null
            ? null
            : IncludeCasReverseDependencies(baselineDocument, changes);
        var alignment = DigestionLedgerAligner.Evaluate(
            migrationDocument,
            snapshot,
            baselineDocument,
            DigestionAlignmentMode.Ingest,
            atomizerResolver,
            changes: evaluationChanges,
            contentKindAtomizerResolver: contentKindAtomizerResolver,
            sourceIds: sourceIds);
        var unverifiedChainParent = migrationDocument.RequireDigestionEntries().FirstOrDefault(entry =>
            (sourceIds is null || sourceIds.Contains(entry.SourceId))
            && entry.Receipts.ChainAtoms.Length > 0
            && alignment.ClausePlanChainParents.Contains(entry.AtomId)
            && !alignment.VerifiedClausePlanParents.Contains(entry.AtomId));
        if (unverifiedChainParent is not null && strategy == DigestionIngestStrategy.AppendOnly)
        {
            Observe(unverifiedChainParent.AtomId, unverifiedChainParent.SourceId, "planned-rewrite");
        }
        else if (unverifiedChainParent is not null)
        {
            var findingPrefix = $"entry {unverifiedChainParent.AtomId} malformed clause chain:";
            var reason = alignment.Findings.FirstOrDefault(finding =>
                finding.StartsWith(findingPrefix, StringComparison.Ordinal));
            throw new FormatException(
                $"ingest clause chain parent {unverifiedChainParent.AtomId} lacks verified clause-plan proof"
                + (reason is null ? string.Empty : $": {reason}"));
        }

        if (alignment.Findings.Length > 0 && strategy != DigestionIngestStrategy.AppendOnly)
        {
            throw new FormatException(
                "ingest alignment is invalid: " + string.Join("; ", alignment.Findings));
        }

        var stale = alignment.ActualStale.ToHashSet(StringComparer.Ordinal);
        var residualBySource = alignment.Residual
            .GroupBy(static item => item.SourceId, StringComparer.Ordinal)
            .ToDictionary(static group => group.Key, static group => group.ToArray(), StringComparer.Ordinal);
        var clausePlansBySource = alignment.ClausePlans
            .GroupBy(static item => item.SourceId, StringComparer.Ordinal)
            .ToDictionary(static group => group.Key, static group => group.ToArray(), StringComparer.Ordinal);
        var globalEntries = migrationDocument.RequireDigestionEntries()
            .ToDictionary(static entry => entry.AtomId, StringComparer.Ordinal);
        var sources = ImmutableArray.CreateBuilder<DigestionLedgerSource>();
        var casObjects = new Dictionary<string, DigestionCasObject>(StringComparer.Ordinal);
        var newAtomIds = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var staleAcknowledged = 0;
        var residualOpenAdded = 0;
        foreach (var source in migrationDocument.RequireDigestionSources())
        {
            if (sourceIds is not null && !sourceIds.Contains(source.SourceId))
            {
                sources.Add(source);
                continue;
            }
            var hasResolvedGenre = alignment.GenreRegistryChecks.TryGetValue(
                source.SourceId,
                out var genreRegistryCheck);
            if (strategy == DigestionIngestStrategy.AppendOnly
                && existingSourceIds.Contains(source.SourceId)
                && hasResolvedGenre
                && !Equals(source.GenreRegistryCheck, genreRegistryCheck))
            {
                foreach (var entry in source.Entries)
                    Observe(entry.AtomId, source.SourceId, "genre-projection-changed");
            }
            var resolvedSource = hasResolvedGenre
                    ? source with
                    {
                        GenreRegistryProjection = GenreRegistryProjection.Available(genreRegistryCheck!),
                    }
                    : source;
            if (!AtomizerRegistry.IsRegistered(source.Atomizer))
            {
                if (source.Atomizer != AtomizerRegistry.NoAtomizerId)
                {
                    throw new FormatException($"ingest source {source.SourceId} has unknown atomizer {source.Atomizer}");
                }

                sources.Add(strategy == DigestionIngestStrategy.AppendOnly
                        && existingSourceIds.Contains(source.SourceId)
                    ? source
                    : resolvedSource);
                continue;
            }

            var acknowledgments = source.Entries
                .Where(entry => stale.Contains(entry.AtomId))
                .Select(static entry => entry.AtomId)
                .Order(StringComparer.Ordinal)
                .ToImmutableArray();
            var priorAcknowledgments = source.AcknowledgedStale.ToHashSet(StringComparer.Ordinal);
            if (strategy == DigestionIngestStrategy.AppendOnly
                && !acknowledgments.SequenceEqual(source.AcknowledgedStale, StringComparer.Ordinal))
            {
                foreach (var atomId in acknowledgments
                             .Concat(source.AcknowledgedStale)
                             .Distinct(StringComparer.Ordinal))
                {
                    Observe(atomId, source.SourceId, "acknowledged-stale-changed");
                }
            }
            var entries = source.Entries.ToBuilder();
            if (residualBySource.TryGetValue(source.SourceId, out var residual))
            {
                foreach (var item in residual)
                {
                    if (globalEntries.TryGetValue(item.SuggestedAtomId, out var existing))
                    {
                        if (!DigestionLedgerAligner.FingerprintsMatch(
                                existing.Fingerprints,
                                item.Atom.Fingerprints))
                        {
                            throw new FormatException(
                                $"ingest atom id collision at {item.SuggestedAtomId}");
                        }
                        continue;
                    }
                    if (strategy == DigestionIngestStrategy.AppendOnly
                        && reservedRemovedAtomIds.Contains(item.SuggestedAtomId))
                    {
                        continue;
                    }

                    var captured = AddCasObject(item.Atom.RawBytes.AsSpan(), casObjects);
                    var priorGenerations = source.Entries
                        .Where(entry => entry.Fingerprints.RawSha256
                            == item.Atom.Fingerprints.RawSha256)
                        .ToArray();
                    var inheritedCoverage = ImmutableArray<DigestionCoverageEdge>.Empty;
                    var inheritedUnresolvedSubitems = priorGenerations
                        .SelectMany(static entry => entry.Receipts.UnresolvedSubitems)
                        .Distinct(StringComparer.Ordinal)
                        .ToImmutableArray();
                    acknowledgments = acknowledgments
                        .Concat(priorGenerations
                            .Select(static entry => entry.AtomId)
                            .Where(priorAcknowledgments.Contains))
                        .Distinct(StringComparer.Ordinal)
                        .Order(StringComparer.Ordinal)
                        .ToImmutableArray();
                    var admitted = new DigestionLedgerEntry(
                        source.SourceId,
                        source.SourcePath,
                        source.Atomizer,
                        item.SuggestedAtomId,
                        item.Atom.Fingerprints,
                        Coverage: inheritedCoverage,
                        new DigestionReceipts([], inheritedUnresolvedSubitems, [], null),
                        item.ProjectedStatus,
                        CasRef: captured.Reference);
                    if (!globalEntries.TryAdd(admitted.AtomId, admitted))
                        continue;
                    entries.Add(admitted);
                    newAtomIds.Add(admitted.AtomId);
                    residualOpenAdded++;
                }
            }


            if (clausePlansBySource.TryGetValue(source.SourceId, out var clausePlans))
            {
                foreach (var clausePlan in clausePlans)
                {
                    var clauseParentId =
                        clausePlan.Parent.Fingerprints.RawSha256["sha256:".Length..];
                    var parentIndexes = entries
                        .Select((entry, index) => (Entry: entry, Index: index))
                        .Where(item => DigestionLedgerAligner.FingerprintsMatch(
                                item.Entry.Fingerprints,
                                clausePlan.Parent.Fingerprints))
                        .ToArray();
                    if (parentIndexes.Length == 0
                        && strategy == DigestionIngestStrategy.AppendOnly
                        && reservedRemovedAtomIds.Contains(clauseParentId))
                    {
                        continue;
                    }
                    if (parentIndexes.Length == 0
                        && globalEntries.ContainsKey(clauseParentId))
                    {
                        Observe(
                            clauseParentId,
                            source.SourceId,
                            "clause-parent-deduplicated");
                        continue;
                    }
                    if (parentIndexes.Length != 1)
                    {
                        throw new FormatException(
                            $"ingest clause plan parent {clausePlan.Parent.Fingerprints.RawSha256} resolves to "
                            + $"{parentIndexes.Length} ledger entries");
                    }

                    var (parent, parentIndex) = parentIndexes[0];
                    if (strategy == DigestionIngestStrategy.AppendOnly
                        && existingAtomIds.Contains(parent.AtomId))
                    {
                        if (parent.Receipts.ChainAtoms.Length == 0)
                            Observe(parent.AtomId, source.SourceId, "planned-rewrite");
                        continue;
                    }
                    if (parent.Receipts.ChainAtoms.Length > 0)
                    {
                        continue;
                    }

                    if (parent.ProjectedStatus != new DigestionStatus(
                            DigestionMigrationState.Residual,
                            DigestionTruthState.Open))
                    {
                        continue;
                    }

                    var decomposition = DigestionDecomposition.Materialize(parent, clausePlan.Plan, globalEntries);
                    foreach (var child in decomposition.NewEntries)
                    {
                        if (!globalEntries.TryAdd(child.AtomId, child))
                            continue;
                        entries.Add(child);
                        newAtomIds.Add(child.AtomId);
                        residualOpenAdded++;
                    }
                    foreach (var captured in decomposition.CasObjects)
                        AddCasObject(captured.Bytes.AsSpan(), casObjects);
                    entries[parentIndex] = decomposition.Parent;
                    globalEntries[parent.AtomId] = decomposition.Parent;
                }
            }

            if (strategy != DigestionIngestStrategy.AppendOnly)
            {
                staleAcknowledged += acknowledgments.Count(priorAcknowledgment =>
                    !priorAcknowledgments.Contains(priorAcknowledgment));
            }
            var outputSource = strategy == DigestionIngestStrategy.AppendOnly
                    && existingSourceIds.Contains(source.SourceId)
                ? source
                : resolvedSource;
            sources.Add(outputSource with
            {
                AcknowledgedStale = strategy == DigestionIngestStrategy.AppendOnly
                    ? outputSource.AcknowledgedStale
                    : acknowledgments,
                Entries = entries.ToImmutable(),
            });
        }

        if (strategy == DigestionIngestStrategy.AppendOnly)
        {
            foreach (var source in document.RequireDigestionSources()
                         .Where(source => sourceIds is null || sourceIds.Contains(source.SourceId)))
            foreach (var entry in source.Entries.Where(NeedsIdentityNormalization))
                Observe(entry.AtomId, source.SourceId, "planned-rewrite");
        }

        var admittedDocument = migrationDocument.WithDigestionSources(sources.ToImmutable());
        var allowedCasReferences = admittedDocument.RequireDigestionEntries()
            .Where(entry => newAtomIds.Contains(entry.AtomId))
            .Select(static entry => entry.CasRef)
            .ToHashSet(StringComparer.Ordinal);
        return new DigestionIngestPlan(
            admittedDocument,
            alignment,
            staleAcknowledged,
            residualOpenAdded,
            casObjects.Values
                .Where(item => strategy != DigestionIngestStrategy.AppendOnly
                    || allowedCasReferences.Contains(item.Reference))
                .OrderBy(static item => item.RelativePath, StringComparer.Ordinal)
                .ToImmutableArray(),
            alignment.Fallbacks,
            sourceIds,
            strategy,
            newAtomIds.ToImmutable(),
            observations
                .OrderBy(static item => item.AtomId, StringComparer.Ordinal)
                .ThenBy(static item => item.SourceId, StringComparer.Ordinal)
                .ThenBy(static item => item.Kind, StringComparer.Ordinal)
                .ToImmutableArray());
    }

    private static bool NeedsIdentityNormalization(DigestionLedgerEntry entry)
    {
        if (!DigestionFingerprint.IsCanonicalSha256(entry.Fingerprints.RawSha256)
            || entry.AtomId != entry.Fingerprints.RawSha256["sha256:".Length..])
        {
            return true;
        }

        var residualOpen = new DigestionStatus(
            DigestionMigrationState.Residual,
            DigestionTruthState.Open);
        return entry.Coverage.IsEmpty
                && entry.Receipts.IsEmpty
                && entry.ProjectedStatus != residualOpen
            || !entry.Coverage.SequenceEqual(entry.Coverage
                .OrderBy(static edge => edge.Gid, StringComparer.Ordinal))
            || !entry.Receipts.Scribe.SequenceEqual(entry.Receipts.Scribe
                .OrderBy(static receipt => receipt.Gid, StringComparer.Ordinal))
            || !entry.Receipts.UnresolvedSubitems.SequenceEqual(
                entry.Receipts.UnresolvedSubitems
                    .Distinct(StringComparer.Ordinal)
                    .Order(StringComparer.Ordinal),
                StringComparer.Ordinal);
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

    internal static BackfillInventoryDocument NormalizeAtomIdentities(
        BackfillInventoryDocument document,
        ImmutableHashSet<string>? sourceIds = null)
    {
        var sources = document.RequireDigestionSources();
        var items = sources
            .Where(source => sourceIds is null || sourceIds.Contains(source.SourceId))
            .SelectMany((source, sourceIndex) => source.Entries.Select((entry, entryIndex) =>
                (Source: source, SourceIndex: sourceIndex, Entry: entry, EntryIndex: entryIndex)))
            .ToArray();
        var oldToNew = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var item in items)
        {
            if (!DigestionFingerprint.IsCanonicalSha256(item.Entry.Fingerprints.RawSha256))
            {
                throw new FormatException(
                    $"entry {item.Entry.AtomId} raw fingerprint is not canonical sha256");
            }

            var atomId = item.Entry.Fingerprints.RawSha256["sha256:".Length..];
            if (oldToNew.TryGetValue(item.Entry.AtomId, out var existing) && existing != atomId)
            {
                throw new FormatException(
                    $"ledger atom_id {item.Entry.AtomId} names multiple content hashes");
            }

            oldToNew[item.Entry.AtomId] = atomId;
        }

        string Remap(string atomId) => oldToNew.GetValueOrDefault(atomId, atomId);

        var entriesBySource = sources.ToDictionary(
            static source => source.SourceId,
            static _ => ImmutableArray.CreateBuilder<DigestionLedgerEntry>(),
            StringComparer.Ordinal);
        foreach (var group in items.GroupBy(
                     static item => item.Entry.Fingerprints.RawSha256,
                     StringComparer.Ordinal))
        {
            var members = group
                .OrderBy(static item => item.Source.SourceId, StringComparer.Ordinal)
                .ThenBy(static item => item.Entry.AtomId, StringComparer.Ordinal)
                .ToArray();
            var owner = members[0];
            var atomId = group.Key["sha256:".Length..];
            var expectedReference = "sha256:" + atomId;
            if (members.Any(item => item.Entry.CasRef != expectedReference))
            {
                throw new FormatException($"atom {atomId} CAS reference differs from its content hash");
            }

            var normalizedFingerprints = members
                .Select(static item => item.Entry.Fingerprints.NormalizedSha256)
                .Distinct(StringComparer.Ordinal)
                .ToArray();
            if (normalizedFingerprints.Length != 1)
            {
                throw new FormatException($"atom {atomId} has conflicting normalized fingerprints");
            }

            var statuses = members
                .Select(static item => item.Entry.ProjectedStatus)
                .Distinct()
                .ToArray();
            if (statuses.Length != 1)
            {
                throw new FormatException($"atom {atomId} has conflicting statuses");
            }

            var coverage = MergeCoverageEdges(atomId, members.SelectMany(
                static item => item.Entry.Coverage));
            var scribe = MergeScribeReceipts(atomId, members.SelectMany(
                static item => item.Entry.Receipts.Scribe));
            var chainCandidates = members
                .Select(item => item.Entry.Receipts.ChainAtoms.Select(Remap).ToImmutableArray())
                .Where(static chain => !chain.IsEmpty)
                .ToArray();
            var chain = chainCandidates.FirstOrDefault();
            if (chainCandidates.Any(candidate => !candidate.SequenceEqual(chain, StringComparer.Ordinal)))
            {
                throw new FormatException($"atom {atomId} has conflicting clause chains");
            }

            var tail = SingleOptional(
                atomId,
                "tail authorization",
                members.Select(static item => item.Entry.Receipts.TailAuthorization));
            var quarantine = SingleOptional(
                atomId,
                "quarantine",
                members.Select(static item => item.Entry.Receipts.Quarantine));
            var disposition = SingleCoverDisposition(
                atomId,
                members.Select(static item => item.Entry.Receipts.CoverDisposition));
            if (!coverage.IsEmpty && (quarantine is not null || disposition is not null))
            {
                throw new FormatException(
                    $"atom {atomId} merged coverage conflicts with quarantine or disposition");
            }

            entriesBySource[owner.Source.SourceId].Add(new DigestionLedgerEntry(
                owner.Source.SourceId,
                owner.Source.SourcePath,
                owner.Source.Atomizer,
                atomId,
                new DigestionFingerprints(group.Key, normalizedFingerprints[0]),
                coverage,
                new DigestionReceipts(
                    scribe,
                    members.SelectMany(static item => item.Entry.Receipts.UnresolvedSubitems)
                        .Distinct(StringComparer.Ordinal)
                        .Order(StringComparer.Ordinal)
                        .ToImmutableArray(),
                    chain.IsDefault ? [] : chain,
                    tail,
                    quarantine,
                    disposition),
                statuses[0],
                expectedReference));
        }

        return document.WithDigestionSources(sources.Select(source =>
            sourceIds is not null && !sourceIds.Contains(source.SourceId) ? source : source with
        {
            AcknowledgedStale = source.AcknowledgedStale
                .Select(Remap)
                .Distinct(StringComparer.Ordinal)
                .Order(StringComparer.Ordinal)
                .ToImmutableArray(),
            Entries = entriesBySource[source.SourceId]
                .OrderBy(static entry => entry.AtomId, StringComparer.Ordinal)
                .ToImmutableArray(),
        }).ToImmutableArray());
    }

    private static ImmutableArray<DigestionCoverageEdge> MergeCoverageEdges(
        string atomId,
        IEnumerable<DigestionCoverageEdge> edges) =>
        edges.GroupBy(static edge => edge.Gid, StringComparer.Ordinal)
            .OrderBy(static group => group.Key, StringComparer.Ordinal)
            .Select(group =>
            {
                var values = group.Distinct().ToArray();
                return values.Length == 1
                    ? values[0]
                    : throw new FormatException(
                        $"atom {atomId} has conflicting coverage edges for {group.Key}");
            })
            .ToImmutableArray();

    private static ImmutableArray<DigestionScribeReceipt> MergeScribeReceipts(
        string atomId,
        IEnumerable<DigestionScribeReceipt> receipts) =>
        receipts.GroupBy(static receipt => receipt.Gid, StringComparer.Ordinal)
            .OrderBy(static group => group.Key, StringComparer.Ordinal)
            .Select(group =>
            {
                var values = group.Distinct().ToArray();
                return values.Length == 1
                    ? values[0]
                    : throw new FormatException(
                        $"atom {atomId} has conflicting scribe receipts for {group.Key}");
            })
            .ToImmutableArray();

    private static T? SingleOptional<T>(
        string atomId,
        string label,
        IEnumerable<T?> values)
        where T : class
    {
        var present = values.Where(static value => value is not null).Cast<T>().Distinct().ToArray();
        return present.Length switch
        {
            0 => null,
            1 => present[0],
            _ => throw new FormatException($"atom {atomId} has conflicting {label}"),
        };
    }

    private static DigestionCoverDisposition? SingleCoverDisposition(
        string atomId,
        IEnumerable<DigestionCoverDisposition?> values)
    {
        var present = values.Where(static value => value is not null).Cast<DigestionCoverDisposition>().ToArray();
        if (present.Length == 0)
        {
            return null;
        }

        var first = present[0];
        if (present.Skip(1).Any(value =>
                value.Outcome != first.Outcome
                || !value.Gids.SequenceEqual(first.Gids, StringComparer.Ordinal)
                || !value.Gaps.SequenceEqual(first.Gaps)))
        {
            throw new FormatException($"atom {atomId} has conflicting cover dispositions");
        }

        return first;
    }

}
