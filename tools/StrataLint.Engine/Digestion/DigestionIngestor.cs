using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;

namespace StrataLint.Engine;

internal sealed record DigestionIngestPlan(
    BackfillInventoryDocument Document,
    int StaleAcknowledged,
    int ResidualOpenAdded,
    ImmutableArray<DigestionCasObject> CasObjects,
    ImmutableArray<DigestionIngestFallback> Fallbacks);

internal static class DigestionSourceConflictMarkers
{
    internal const string DiagnosticCode = "INGEST-CONFLICT-MARKER-001";

    internal static int? FindFirstLine(ReadOnlySpan<byte> bytes)
    {
        var start = bytes.Length >= 3
            && bytes[0] == 0xef
            && bytes[1] == 0xbb
            && bytes[2] == 0xbf
                ? 3
                : 0;
        var lineNumber = 1;
        while (true)
        {
            var end = start;
            while (end < bytes.Length
                && bytes[end] != (byte)'\r'
                && bytes[end] != (byte)'\n')
            {
                end++;
            }

            var line = bytes[start..end];
            if (line.StartsWith("<<<<<<< "u8)
                || line.StartsWith("||||||| "u8)
                || line.SequenceEqual("======="u8)
                || line.StartsWith(">>>>>>> "u8))
            {
                return lineNumber;
            }

            if (end == bytes.Length)
            {
                return null;
            }

            if (bytes[end] == (byte)'\r'
                && end + 1 < bytes.Length
                && bytes[end + 1] == (byte)'\n')
            {
                end++;
            }

            start = end + 1;
            lineNumber++;
        }
    }

    internal static string FormatFinding(string sourcePath, int line) =>
        $"{DiagnosticCode} {sourcePath}:{line}: unresolved merge conflict marker in digestion source";
}

internal static class DigestionIngestor
{
    /// <summary>
    /// Every theory document is digested by something. A volume nobody has written a
    /// dialect for used to sit in the tree with no source declaration at all — not refused,
    /// not digested, just unaccounted — because the declaration was a hand-written file and
    /// nothing checked that one existed. It is derivable from the path, so ingest derives
    /// it: the default atomizer, and a source id slugged from the file name. What remains
    /// hand-written is only what is genuinely a decision — that this path is a canonical
    /// volume at all, which stays with <c>governance_documents</c> on the base side.
    /// </summary>
    private static BackfillInventoryDocument RegisterDefaultTheorySources(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot)
    {
        var sources = document.RequireDigestionSources();
        var declaredPaths = sources
            .Select(static source => source.SourcePath)
            .ToHashSet(StringComparer.Ordinal);
        var sourceIds = sources.ToDictionary(
            static source => source.SourceId,
            static source => source.SourcePath,
            StringComparer.Ordinal);
        var registered = ImmutableArray.CreateBuilder<DigestionLedgerSource>();
        foreach (var path in snapshot.Files.Keys
                     .Select(static path => path.Value)
                     .Where(static path => path.StartsWith(
                         DigestionOpaquePathPolicy.TheoryRootPath,
                         StringComparison.Ordinal))
                     .Where(path => !declaredPaths.Contains(path))
                     .Order(StringComparer.Ordinal))
        {
            var sourceId = DeriveSourceId(path);
            if (sourceIds.TryGetValue(sourceId, out var claimant))
            {
                throw new FormatException(
                    $"theory source id derived from {path} collides with {claimant}: {sourceId}");
            }

            sourceIds.Add(sourceId, path);
            registered.Add(new DigestionLedgerSource(
                sourceId,
                path,
                AtomizerRegistry.GenericId,
                [],
                GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry),
                ImmutableArray<DigestionLedgerEntry>.Empty));
        }

        return registered.Count == 0
            ? document
            : document.WithDigestionSources(sources.AddRange(registered));
    }

    /// <summary>
    /// The file name, lowercased, with every run of non-alphanumerics collapsed to a dash —
    /// the shape <c>BackfillInventoryRule</c> already requires of a source id.
    /// </summary>
    private static string DeriveSourceId(string path)
    {
        var stem = Path.GetFileNameWithoutExtension(path);
        var id = new string(stem.Select(static character =>
            char.IsAsciiLetterOrDigit(character) ? char.ToLowerInvariant(character) : '-').ToArray());
        id = string.Join('-', id.Split('-', StringSplitOptions.RemoveEmptyEntries));
        return id.Length > 0 ? id : "source-" + DigestionFingerprint.ShortHash(path);
    }

    internal static DigestionIngestPlan Plan(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        BackfillInventoryDocument baselineDocument,
        RepositorySnapshot? baselineSnapshot = null,
        Func<string, TheoryAtomizer>? atomizerResolver = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(baselineDocument);

        var migrationDocument = RegisterDefaultTheorySources(
            PrepareLegacyMigrations(document),
            snapshot);
        var alignment = DigestionLedgerAligner.Evaluate(
            migrationDocument,
            snapshot,
            baselineDocument,
            DigestionAlignmentMode.Ingest,
            atomizerResolver);
        var unverifiedChainParent = migrationDocument.RequireDigestionEntries().FirstOrDefault(entry =>
            entry.Receipts.ChainAtoms.Length > 0
            && alignment.ClausePlanChainParents.Contains(entry.AtomId)
            && !alignment.VerifiedClausePlanParents.Contains(entry.AtomId));
        if (unverifiedChainParent is not null)
        {
            var findingPrefix = $"entry {unverifiedChainParent.AtomId} malformed clause chain:";
            var reason = alignment.Findings.FirstOrDefault(finding =>
                finding.StartsWith(findingPrefix, StringComparison.Ordinal));
            throw new FormatException(
                $"ingest clause chain parent {unverifiedChainParent.AtomId} lacks verified clause-plan proof"
                + (reason is null ? string.Empty : $": {reason}"));
        }

        if (alignment.Findings.Length > 0)
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
        var atomIds = migrationDocument.RequireDigestionEntries()
            .Select(static entry => entry.AtomId)
            .ToHashSet(StringComparer.Ordinal);
        var sources = ImmutableArray.CreateBuilder<DigestionLedgerSource>();
        var casObjects = new Dictionary<string, DigestionCasObject>(StringComparer.Ordinal);
        var staleAcknowledged = 0;
        var residualOpenAdded = 0;
        foreach (var source in migrationDocument.RequireDigestionSources())
        {
            var resolvedSource = alignment.GenreRegistryChecks.TryGetValue(
                source.SourceId,
                out var genreRegistryCheck)
                    ? source with
                    {
                        GenreRegistryProjection = GenreRegistryProjection.Available(genreRegistryCheck),
                    }
                    : source;
            if (!AtomizerRegistry.IsRegistered(source.Atomizer))
            {
                if (source.Atomizer != AtomizerRegistry.NoAtomizerId)
                {
                    throw new FormatException($"ingest source {source.SourceId} has unknown atomizer {source.Atomizer}");
                }

                sources.Add(CaptureBoundarySource(resolvedSource, snapshot, casObjects));
                continue;
            }

            if (source.Entries.Length > 0
                && !source.Entries.Any(static entry => entry.Boundary is null))
            {
                sources.Add(resolvedSource);
                continue;
            }

            var acknowledgments = source.Entries
                .Where(entry => stale.Contains(entry.AtomId))
                .Select(static entry => entry.AtomId)
                .Order(StringComparer.Ordinal)
                .ToImmutableArray();
            var priorAcknowledgments = source.AcknowledgedStale.ToHashSet(StringComparer.Ordinal);
            var entries = source.Entries.ToBuilder();
            foreach (var reclassification in alignment.GenreReclassifications.Where(item =>
                         item.SourceId == source.SourceId))
            {
                var matches = entries
                    .Select((entry, index) => (Entry: entry, Index: index))
                    .Where(item => item.Entry.AtomId == reclassification.AtomId)
                    .ToArray();
                if (matches.Length != 1)
                {
                    throw new FormatException(
                        $"ingest genre reclassification atom_id resolves to {matches.Length} entries: "
                        + reclassification.AtomId);
                }

                var (entry, index) = matches[0];
                entries[index] = entry with
                {
                    AstPath = reclassification.AstPath,
                };
            }

            if (residualBySource.TryGetValue(source.SourceId, out var residual))
            {
                foreach (var item in residual)
                {
                    if (!atomIds.Add(item.SuggestedAtomId))
                    {
                        var matches = entries
                            .Select((entry, index) => (Entry: entry, Index: index))
                            .Where(match => match.Entry.AtomId == item.SuggestedAtomId)
                            .ToArray();
                        if (matches.Length == 1
                            && AstPathKind(matches[0].Entry.AstPath)
                                == AstPathKind(item.Atom.AstPath)
                            && (stale.Contains(matches[0].Entry.AtomId)
                                || !alignment.IsProduced(
                                    source.SourceId,
                                    matches[0].Entry.AstPath)))
                        {
                            var (entry, index) = matches[0];
                            entries[index] = entry with { AstPath = item.Atom.AstPath };
                            acknowledgments = acknowledgments
                                .Where(atomId => atomId != entry.AtomId)
                                .ToImmutableArray();
                            continue;
                        }

                        throw new FormatException(
                            $"ingest residual atom_id collides with the ledger: {item.SuggestedAtomId}");
                    }

                    var captured = AddCasObject(item.Atom.RawBytes.AsSpan(), casObjects);
                    var priorGenerations = source.Entries
                        .Where(entry => entry.AstPath == item.Atom.AstPath)
                        .ToArray();
                    var receiptedCoverage = baselineSnapshot is null
                        ? ImmutableHashSet<string>.Empty
                        : DigestionFormalizationPrecommitmentValidator.RegisteredBaseOwnedGids(
                            baselineSnapshot,
                            item.SuggestedAtomId,
                            item.Atom.Fingerprints.RawSha256);
                    var inheritedCoverage = priorGenerations
                        .SelectMany(static entry => entry.CoverageGids)
                        .Distinct(StringComparer.Ordinal)
                        .Where(receiptedCoverage.Contains)
                        .ToImmutableArray();
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
                    entries.Add(new DigestionLedgerEntry(
                        source.SourceId,
                        source.SourcePath,
                        source.Atomizer,
                        item.SuggestedAtomId,
                        item.Atom.AstPath,
                        Boundary: null,
                        item.Atom.Fingerprints,
                        CoverageGids: inheritedCoverage,
                        new DigestionReceipts([], [], inheritedUnresolvedSubitems, [], null),
                        item.ProjectedStatus,
                        CasRef: captured.Reference));
                    residualOpenAdded++;
                }
            }


            if (clausePlansBySource.TryGetValue(source.SourceId, out var clausePlans))
            {
                foreach (var clausePlan in clausePlans)
                {
                    var parentIndexes = entries
                        .Select((entry, index) => (Entry: entry, Index: index))
                        .Where(item => item.Entry.AstPath == clausePlan.Plan.ParentAstPath
                            && DigestionLedgerAligner.FingerprintsMatch(
                                item.Entry.Fingerprints,
                                clausePlan.Parent.Fingerprints))
                        .ToArray();
                    if (parentIndexes.Length != 1)
                    {
                        throw new FormatException(
                            $"ingest clause plan parent {clausePlan.Plan.ParentAstPath} resolves to "
                            + $"{parentIndexes.Length} ledger entries");
                    }

                    var (parent, parentIndex) = parentIndexes[0];
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

                    var childIds = ImmutableArray.CreateBuilder<string>(clausePlan.Plan.Children.Length);
                    foreach (var (child, childIndex) in clausePlan.Plan.Children.Select(
                                 (child, index) => (Child: child, Index: index)))
                    {
                        var childId = ClauseAtomId(source, parent, child, childIndex);
                        if (!atomIds.Add(childId))
                        {
                            throw new FormatException(
                                $"ingest clause atom_id collides with the ledger: {childId}");
                        }

                        var captured = AddCasObject(child.RawBytes.AsSpan(), casObjects);
                        entries.Add(new DigestionLedgerEntry(
                            source.SourceId,
                            source.SourcePath,
                            source.Atomizer,
                            childId,
                            child.AstPath,
                            Boundary: null,
                            child.Fingerprints,
                            CoverageGids: [],
                            new DigestionReceipts([], [], [], [], null),
                            new DigestionStatus(
                                DigestionMigrationState.Residual,
                                DigestionTruthState.Open),
                            CasRef: captured.Reference));
                        childIds.Add(childId);
                        residualOpenAdded++;
                    }

                    entries[parentIndex] = parent with
                    {
                        Receipts = parent.Receipts with
                        {
                            UnresolvedSubitems = [],
                            ChainAtoms = childIds.MoveToImmutable(),
                        },
                    };
                }
            }

            staleAcknowledged += acknowledgments.Count(priorAcknowledgment =>
                !priorAcknowledgments.Contains(priorAcknowledgment));
            sources.Add(resolvedSource with
            {
                AcknowledgedStale = acknowledgments,
                Entries = entries.ToImmutable(),
            });
        }

        return new DigestionIngestPlan(
            migrationDocument.WithDigestionSources(sources.ToImmutable()),
            staleAcknowledged,
            residualOpenAdded,
            casObjects.Values
                .OrderBy(static item => item.RelativePath, StringComparer.Ordinal)
                .ToImmutableArray(),
            alignment.Fallbacks);
    }

    private static string ClauseAtomId(
        DigestionLedgerSource source,
        DigestionLedgerEntry parent,
        DigestionAtom child,
        int childIndex)
    {
        var stem = AtomizerRegistry.Require(source.Atomizer).ResidualPrefix
            + "-residual-"
            + child.Fingerprints.RawSha256["sha256:".Length..];
        var occurrenceBytes = Encoding.UTF8.GetBytes(
            parent.AtomId + "\0" + child.AstPath + "\0" + childIndex);
        return stem + "-" + Convert.ToHexStringLower(SHA256.HashData(occurrenceBytes));
    }

    private static DigestionLedgerSource CaptureBoundarySource(
        DigestionLedgerSource source,
        RepositorySnapshot snapshot,
        IDictionary<string, DigestionCasObject> casObjects)
    {
        if (!snapshot.TryGetFile(source.SourcePath, out var sourceFile))
        {
            throw new FormatException($"ingest source path is dangling: {source.SourcePath}");
        }

        return source with
        {
            Entries = source.Entries
                .Select(entry => CaptureBoundaryEntry(
                    entry,
                    sourceFile.RawBytes,
                    snapshot,
                    casObjects))
                .ToImmutableArray(),
        };
    }

    private static DigestionLedgerEntry CaptureBoundaryEntry(
        DigestionLedgerEntry entry,
        ImmutableArray<byte> sourceBytes,
        RepositorySnapshot snapshot,
        IDictionary<string, DigestionCasObject> casObjects)
    {
        var existingBoundary = entry.Boundary
            ?? throw new FormatException(
                $"ingest no-atomizer entry {entry.AtomId} has no boundary");
        var casPath = DigestionCasStore.RootPath + entry.CasRef["sha256:".Length..];
        if (!snapshot.TryGetFile(casPath, out var blob))
        {
            throw new FormatException(
                $"ingest entry {entry.AtomId} CAS blob is missing: {casPath}");
        }

        var casObject = DigestionCasStore.Capture(blob.RawBytes.AsSpan());
        if (casObject.Reference != entry.CasRef)
        {
            throw new FormatException(
                $"ingest entry {entry.AtomId} CAS blob hash mismatch: {casPath}");
        }

        var receiptBytes = blob.RawBytes.AsSpan();
        var start = receiptBytes.IsEmpty ? -1 : sourceBytes.AsSpan().IndexOf(receiptBytes);
        if (start < 0)
        {
            throw new FormatException(
                $"ingest entry {entry.AtomId} has no byte-exact match in {entry.SourcePath}");
        }

        if (sourceBytes.AsSpan()[(start + 1)..].IndexOf(receiptBytes) >= 0)
        {
            throw new FormatException(
                $"ingest entry {entry.AtomId} has multiple byte-exact matches in {entry.SourcePath}");
        }

        var rebound = new DigestionBoundary(
            existingBoundary.AstPath,
            start,
            start + receiptBytes.Length);
        return rebound == existingBoundary
            ? entry
            : entry with
            {
                Boundary = rebound,
            };
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

    private static string AstPathKind(string astPath)
    {
        var separator = astPath.IndexOf('/', StringComparison.Ordinal);
        return separator < 0 ? astPath : astPath[..separator];
    }

    private static BackfillInventoryDocument PrepareLegacyMigrations(
        BackfillInventoryDocument document) =>
        document.WithDigestionSources(document.RequireDigestionSources()
            .Select(source => !AtomizerRegistry.IsRegistered(source.Atomizer)
                ? source
                : source with
                {
                    Entries = source.Entries
                        .Select(static entry => entry.Boundary is null
                            ? entry
                            : entry with
                            {
                                Boundary = null,
                            })
                        .ToImmutableArray(),
                })
            .ToImmutableArray());
}
