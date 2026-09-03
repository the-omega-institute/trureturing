using System.Collections.Immutable;
using Trureturing.Truth;

namespace StrataLint.Engine;

internal sealed record DigestionCoverageSchemaMigration(
    BackfillInventoryDocument Document,
    ImmutableDictionary<string, ImmutableArray<byte>> AtomFiles,
    int SourceBindingsValidated,
    int RelationshipsBefore,
    int RelationshipsAfter,
    int ResolvedTargets,
    int NullTargets);

internal static class DigestionCoverageSchemaMigrator
{
    // expand phase (L2a): one-off L2b migration tool; removed in L2c after the L2b data migration
    internal static DigestionCoverageSchemaMigration Migrate(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean) =>
        BackfillInventoryLoader.MigrateCoverageSchema(snapshot, lean);
}

internal static partial class BackfillInventoryLoader
{
    private static readonly string CoverageRelationshipKey = "coverage_" + "gids";
    private static readonly string RetiredSourceKey = "source_" + "sha256";
    private static readonly string RetiredHistoryKey = "statement_id_" + "history";
    private static readonly string RetiredRecordedAtKey = "recorded_at_" + "utc";

    internal static DigestionCoverageSchemaMigration MigrateCoverageSchema(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);

        var metadata = snapshot.Files
            .Where(static pair => pair.Key.Value.StartsWith(RootPath, StringComparison.Ordinal)
                && pair.Key.Value.EndsWith("/source.toml", StringComparison.Ordinal))
            .OrderBy(static pair => pair.Key.Value, StringComparer.Ordinal)
            .ToArray();
        if (metadata.Length == 0)
        {
            throw new FormatException($"digestion backfill directory is missing: {RootPath}");
        }

        foreach (var path in snapshot.Files.Keys
                     .Where(static path => path.Value.StartsWith(RootPath, StringComparison.Ordinal)))
        {
            if (!IsCanonicalPath(path.Value))
            {
                throw new FormatException($"noncanonical digestion ledger path: {path.Value}");
            }
        }

        var sources = ImmutableArray.CreateBuilder<DigestionLedgerSource>();
        var atomPaths = new Dictionary<(string SourceId, string AtomId), string>();
        var relationshipsBefore = new HashSet<(string AtomId, string Gid)>();
        var sourceBindingsValidated = 0;
        foreach (var (metadataPath, metadataFile) in metadata)
        {
            var sourceRoot = metadataPath.Value[..^"source.toml".Length];
            var metadataParse = ParseCandidateSourceMetadata(metadataFile.Text, metadataPath.Value);
            var fields = metadataParse.Fields;
            var sourceId = fields["source_id"].Single();
            if (!string.Equals(sourceRoot, $"{RootPath}{sourceId}/", StringComparison.Ordinal))
            {
                throw new FormatException(
                    $"source metadata path disagrees with source_id: {metadataPath.Value}");
            }

            var entries = ImmutableArray.CreateBuilder<DigestionLedgerEntry>();
            foreach (var (path, file) in snapshot.Files
                         .Where(pair => pair.Key.Value.StartsWith(sourceRoot, StringComparison.Ordinal)
                             && pair.Key.Value.EndsWith(".yaml", StringComparison.Ordinal))
                         .OrderBy(static pair => pair.Key.Value, StringComparer.Ordinal))
            {
                var suffix = path.Value[sourceRoot.Length..];
                var slash = suffix.IndexOf('/');
                var state = suffix[..slash].Split('-');
                var atomId = suffix[(slash + 1)..^".yaml".Length];
                var rawEntry = YamlSubsetParser.Parse(file.Text) as Dictionary<string, object?>
                    ?? throw new FormatException($"backfill atom must be a mapping: {path.Value}");
                var entry = ProjectCoverageMigrationEntry(
                    rawEntry,
                    atomId,
                    path.Value,
                    relationshipsBefore,
                    ref sourceBindingsValidated);
                if (!entry.TryAdd("atom_id", atomId)
                    || !entry.TryAdd("status", new Dictionary<string, object?>(StringComparer.Ordinal)
                    {
                        ["migration"] = state[0],
                        ["truth"] = state[1],
                    }))
                {
                    throw new FormatException($"backfill atom contains path-derived fields: {path.Value}");
                }

                var parsed = BackfillInventoryDocument.ParseEntry(
                    sourceId,
                    fields["path"].Single(),
                    fields["atomizer"].Single(),
                    entry);
                entries.Add(parsed);
                atomPaths.Add((sourceId, atomId), path.Value);
            }

            sources.Add(new DigestionLedgerSource(
                sourceId,
                fields["path"].Single(),
                fields["atomizer"].Single(),
                fields.GetValueOrDefault("acknowledged_stale", []).ToImmutableArray(),
                metadataParse.GenreRegistryProjection,
                entries.ToImmutable()));
        }

        var sourceRoots = metadata
            .Select(static pair => pair.Key.Value[..^"source.toml".Length])
            .ToArray();
        foreach (var atomPath in snapshot.Files.Keys.Where(static path =>
                     path.Value.StartsWith(RootPath, StringComparison.Ordinal)
                     && path.Value.EndsWith(".yaml", StringComparison.Ordinal)))
        {
            if (sourceRoots.Count(root => atomPath.Value.StartsWith(root, StringComparison.Ordinal)) != 1)
            {
                throw new FormatException(
                    $"backfill atom is not owned by exactly one source: {atomPath.Value}");
            }
        }

        var migrated = BackfillInventoryDocument.Create(sources.ToImmutable(), DeriveTickets(snapshot));
        migrated = DigestionCoverageTargetAligner.Align(migrated, snapshot, lean);
        var relationshipsAfter = migrated.RequireDigestionEntries()
            .SelectMany(static entry => entry.Coverage.Select(edge => (entry.AtomId, edge.Gid)))
            .ToHashSet();
        if (!relationshipsBefore.SetEquals(relationshipsAfter))
        {
            throw new InvalidOperationException(
                "coverage migration changed the stable (atom_id, gid) relationship set");
        }

        var atomFiles = migrated.RequireDigestionEntries().ToImmutableDictionary(
            entry => atomPaths[(entry.SourceId, entry.AtomId)],
            BackfillInventoryWriter.WriteAtom,
            StringComparer.Ordinal);
        var resolvedTargets = migrated.RequireDigestionEntries()
            .SelectMany(static entry => entry.Coverage)
            .Count(static edge => edge.TargetStatementId is not null);
        return new DigestionCoverageSchemaMigration(
            migrated,
            atomFiles,
            sourceBindingsValidated,
            relationshipsBefore.Count,
            relationshipsAfter.Count,
            resolvedTargets,
            relationshipsAfter.Count - resolvedTargets);
    }

    private static Dictionary<string, object?> ProjectCoverageMigrationEntry(
        Dictionary<string, object?> entry,
        string atomId,
        string path,
        ISet<(string AtomId, string Gid)> relationships,
        ref int sourceBindingsValidated)
    {
        RequireExactMigrationKeys(
            entry,
            ["fingerprints", "cas_ref", CoverageRelationshipKey, "receipts"],
            path);
        var rawCoverage = MigrationList(entry, CoverageRelationshipKey, path);
        var containsLegacyGid = rawCoverage.Any(static item => item is string);
        var containsCurrentEdge = rawCoverage.Any(static item => item is Dictionary<string, object?>);
        if (containsLegacyGid && containsCurrentEdge)
        {
            throw new FormatException(
                $"coverage_gids cannot mix legacy scalars and current edges: {path}");
        }

        var receipts = MigrationMapping(entry.GetValueOrDefault("receipts"), path + " receipts");
        var hasLegacyCoverageReceipts = receipts.ContainsKey("coverage");
        var hasLegacyRecordedAt = receipts.GetValueOrDefault("cover_disposition")
            is Dictionary<string, object?> rawLegacyDisposition
            && rawLegacyDisposition.ContainsKey(RetiredRecordedAtKey);
        if (!containsLegacyGid
            && (containsCurrentEdge || (!hasLegacyCoverageReceipts && !hasLegacyRecordedAt)))
        {
            foreach (var rawEdge in rawCoverage)
            {
                var edge = MigrationMapping(rawEdge, path + " coverage edge");
                RequireExactMigrationKeys(edge, ["gid", "target_statement_id"], path);
                relationships.Add((atomId, MigrationScalar(edge, "gid", path)));
            }

            return entry;
        }

        var orderedGids = new List<string>();
        var seenGids = new HashSet<string>(StringComparer.Ordinal);
        foreach (var rawGid in rawCoverage)
        {
            AddGid(MigrationScalar(rawGid, path + " relationship"));
        }

        RequireMigrationReceiptKeys(receipts, path);
        foreach (var rawReceipt in MigrationList(receipts, "coverage", path))
        {
            var receipt = MigrationMapping(rawReceipt, path + " coverage receipt");
            RequireCoverageReceiptKeys(receipt, path);
            var gid = MigrationScalar(receipt, "gid", path);
            var source = MigrationScalar(receipt, RetiredSourceKey, path);
            sourceBindingsValidated++;
            if (!string.Equals(source, "sha256:" + atomId, StringComparison.Ordinal))
            {
                throw new FormatException(
                    $"coverage source binding {source} does not match atom_id {atomId}: {path}");
            }

            _ = MigrationScalar(receipt, "target_statement_id", path);
            if (receipt.TryGetValue(RetiredHistoryKey, out var history) && history is not List<object?>)
            {
                throw new FormatException($"coverage history must be a list: {path}");
            }

            AddGid(gid);
        }

        entry[CoverageRelationshipKey] =
            orderedGids.Select(gid => (object?)new Dictionary<string, object?>(StringComparer.Ordinal)
            {
                ["gid"] = gid,
                ["target_statement_id"] = null,
            }).ToList();
        receipts.Remove("coverage");
        if (receipts.GetValueOrDefault("cover_disposition") is Dictionary<string, object?> disposition)
        {
            disposition.Remove(RetiredRecordedAtKey);
        }

        return entry;

        void AddGid(string gid)
        {
            relationships.Add((atomId, gid));
            if (seenGids.Add(gid))
            {
                orderedGids.Add(gid);
            }
        }
    }

    private static void RequireMigrationReceiptKeys(
        IReadOnlyDictionary<string, object?> receipts,
        string path)
    {
        var required = new[] { "coverage", "scribe", "unresolved_subitems" };
        var optional = new[]
        {
            "chain_atoms", "tail_authorization", "quarantine", "cover_disposition",
        };
        var keys = receipts.Keys.ToHashSet(StringComparer.Ordinal);
        if (!required.All(keys.Contains)
            || !keys.IsSubsetOf(required.Concat(optional).ToHashSet(StringComparer.Ordinal)))
        {
            throw new FormatException($"legacy receipts keys are not canonical: {path}");
        }
    }

    private static void RequireCoverageReceiptKeys(
        IReadOnlyDictionary<string, object?> receipt,
        string path)
    {
        var required = new[] { "gid", RetiredSourceKey, "target_statement_id" };
        var allowed = required.Append(RetiredHistoryKey).ToHashSet(StringComparer.Ordinal);
        if (!required.All(receipt.ContainsKey)
            || !receipt.Keys.ToHashSet(StringComparer.Ordinal).IsSubsetOf(allowed))
        {
            throw new FormatException($"legacy coverage receipt keys are not canonical: {path}");
        }
    }

    private static void RequireExactMigrationKeys(
        IReadOnlyDictionary<string, object?> mapping,
        IEnumerable<string> expected,
        string path)
    {
        if (!mapping.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(expected))
        {
            throw new FormatException($"coverage migration keys are not canonical: {path}");
        }
    }

    private static Dictionary<string, object?> MigrationMapping(object? value, string context) =>
        value as Dictionary<string, object?>
        ?? throw new FormatException($"{context} must be a mapping");

    private static List<object?> MigrationList(
        IReadOnlyDictionary<string, object?> mapping,
        string key,
        string context) =>
        mapping.GetValueOrDefault(key) as List<object?>
        ?? throw new FormatException($"{context} {key} must be a list");

    private static string MigrationScalar(
        IReadOnlyDictionary<string, object?> mapping,
        string key,
        string context) =>
        MigrationScalar(mapping.GetValueOrDefault(key), context + " " + key);

    private static string MigrationScalar(object? value, string context) =>
        value is string text && !string.IsNullOrWhiteSpace(text)
            ? text
            : throw new FormatException($"{context} must be a nonempty scalar");
}
