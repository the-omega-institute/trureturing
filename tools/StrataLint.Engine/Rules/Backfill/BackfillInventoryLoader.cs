using System.Collections.Immutable;
using System.Globalization;
using System.Text.RegularExpressions;
using Trureturing.Truth;

namespace StrataLint.Engine;

internal sealed partial class BackfillInventoryDocument
{
    internal static IReadOnlyList<string> EntryFieldUniverse { get; } =
    [
        "atom_id",
        "ast_path",
        "boundary",
        "fingerprints",
        "cas_ref",
        "coverage_gids",
        "receipts",
        "status",
    ];

    private readonly IReadOnlyDictionary<string, object?> root;
    private readonly ImmutableArray<BackfillTicketReference> derivedTickets;
    private readonly ImmutableArray<DigestionLedgerSource> projectedSources;

    private BackfillInventoryDocument(
        IReadOnlyDictionary<string, object?> root,
        ImmutableArray<BackfillTicketReference> derivedTickets,
        ImmutableArray<DigestionLedgerSource> projectedSources)
    {
        this.root = root;
        this.derivedTickets = derivedTickets;
        this.projectedSources = projectedSources;
    }

    internal IReadOnlyDictionary<string, object?> Root => root;

    internal static BackfillInventoryDocument Create(
        ImmutableArray<DigestionLedgerSource> sources,
        ImmutableArray<BackfillTicketReference> tickets)
    {
        var root = new Dictionary<string, object?>(StringComparer.Ordinal)
        {
            ["schema_version"] = BackfillInventoryLoader.SchemaVersion,
            ["ledger"] = BackfillInventoryLoader.LedgerName,
            ["sources"] = new List<object?>(),
        };
        return new BackfillInventoryDocument(root, tickets, sources);
    }

    internal ImmutableArray<BackfillTicketReference> RequireTickets() => derivedTickets;

    internal ImmutableArray<DigestionLedgerSource> RequireDigestionSources() => projectedSources;

    internal ImmutableArray<DigestionLedgerEntry> RequireDigestionEntries() =>
        RequireDigestionSources().SelectMany(static source => source.Entries).ToImmutableArray();

    internal BackfillInventoryDocument WithDigestionSources(
        ImmutableArray<DigestionLedgerSource> sources) =>
        new(root, RequireTickets(), sources);

    internal ImmutableArray<string> RequireReferencedGids()
    {
        var gids = ImmutableArray.CreateBuilder<string>();
        var seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (var entry in RequireDigestionEntries())
        {
            foreach (var gid in entry.CoverageGids)
            {
                if (seen.Add(gid)) gids.Add(gid);
            }
        }

        foreach (var ticket in RequireTickets())
        {
            if (seen.Add(ticket.Gid)) gids.Add(ticket.Gid);
        }

        return gids.ToImmutable();
    }

    internal static DigestionLedgerEntry ParseEntry(
        string sourceId,
        string sourcePath,
        string atomizer,
        object? rawEntry,
        bool allowLegacyCoverageReceipts = false)
    {
        var entry = Mapping(rawEntry, $"source {sourceId} entries must be mappings");
        var hasBoundary = entry.ContainsKey("boundary");
        var excludedBoundaryField = hasBoundary ? "ast_path" : "boundary";
        var expectedKeys = EntryFieldUniverse
            .Where(field => !string.Equals(field, excludedBoundaryField, StringComparison.Ordinal))
            .ToArray();
        ExactKeys(
            entry,
            expectedKeys,
            $"source {sourceId} entry");
        var atomId = Scalar(entry, "atom_id", $"source {sourceId} atom_id");

        DigestionBoundary? parsedBoundary = null;
        string astPath;
        if (hasBoundary)
        {
            var boundary = Mapping(
                entry.GetValueOrDefault("boundary"),
                $"entry {atomId} boundary must be a mapping");
            ExactKeys(boundary, ["ast_path", "start_byte", "end_byte"], $"entry {atomId} boundary");
            parsedBoundary = new DigestionBoundary(
                Scalar(boundary, "ast_path", $"entry {atomId} ast_path"),
                Integer(boundary, "start_byte", $"entry {atomId} start_byte"),
                Integer(boundary, "end_byte", $"entry {atomId} end_byte"));
            astPath = parsedBoundary.AstPath;
        }
        else
        {
            astPath = Scalar(entry, "ast_path", $"entry {atomId} ast_path");
        }

        var fingerprints = Mapping(
            entry.GetValueOrDefault("fingerprints"),
            $"entry {atomId} fingerprints must be a mapping");
        ExactKeys(fingerprints, ["raw_sha256", "normalized_sha256"], $"entry {atomId} fingerprints");
        var parsedFingerprints = new DigestionFingerprints(
            Scalar(fingerprints, "raw_sha256", $"entry {atomId} raw_sha256"),
            Scalar(fingerprints, "normalized_sha256", $"entry {atomId} normalized_sha256"));

        var coverageGids = Strings(
            List(entry, "coverage_gids", $"entry {atomId} coverage_gids must be a list"),
            $"entry {atomId} coverage_gids");
        var receipts = ParseReceipts(
            atomId,
            entry.GetValueOrDefault("receipts"),
            allowLegacyCoverageReceipts);
        if (receipts.Quarantine is not null && coverageGids.Length > 0)
        {
            throw new FormatException(
                $"entry {atomId} cannot be quarantined because coverage_gids provides a machine-form statement");
        }

        if (receipts.CoverDisposition is not null && coverageGids.Length > 0)
        {
            throw new FormatException(
                $"entry {atomId} cover_disposition cannot coexist with coverage_gids");
        }

        if (receipts.CoverDisposition is not null && receipts.Quarantine is not null)
        {
            throw new FormatException(
                $"entry {atomId} cover_disposition cannot coexist with quarantine");
        }

        var status = Mapping(entry.GetValueOrDefault("status"), $"entry {atomId} status must be a mapping");
        ExactKeys(status, ["migration", "truth"], $"entry {atomId} status");

        return new DigestionLedgerEntry(
            sourceId,
            sourcePath,
            atomizer,
            atomId,
            astPath,
            parsedBoundary,
            parsedFingerprints,
            coverageGids,
            receipts,
            new DigestionStatus(
                ParseMigration(Scalar(status, "migration", $"entry {atomId} migration")),
                ParseTruth(Scalar(status, "truth", $"entry {atomId} truth"))),
            Scalar(entry, "cas_ref", $"entry {atomId} cas_ref"));
    }

    private static DigestionCoverDisposition? ParseCoverDisposition(
        string atomId,
        IReadOnlyDictionary<string, object?> receipts)
    {
        if (!receipts.ContainsKey("cover_disposition"))
        {
            return null;
        }

        var raw = Mapping(
            receipts.GetValueOrDefault("cover_disposition"),
            $"entry {atomId} cover_disposition must be a mapping");
        ExactKeys(raw, ["outcome", "recorded_at_utc", "gids", "gaps"],
            $"entry {atomId} cover_disposition");

        var outcomeText = Scalar(raw, "outcome", $"entry {atomId} cover_disposition outcome");
        var separator = outcomeText.IndexOf('-', StringComparison.Ordinal);
        if (separator <= 0 || separator != outcomeText.LastIndexOf("-", StringComparison.Ordinal))
        {
            throw new FormatException(
                $"entry {atomId} cover_disposition outcome must be a canonical digestion status");
        }

        var outcome = new DigestionStatus(
            ParseMigration(outcomeText[..separator]),
            ParseTruth(outcomeText[(separator + 1)..]));
        var gids = Strings(
            List(raw, "gids", $"entry {atomId} cover_disposition gids must be a list"),
            $"entry {atomId} cover_disposition gids");
        if (gids.IsEmpty
            || gids.Any(static gid => !Gid.TryParse(gid, out _))
            || !gids.SequenceEqual(
                gids.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal),
                StringComparer.Ordinal))
        {
            throw new FormatException(
                $"entry {atomId} cover_disposition gids must be sorted unique nonempty values");
        }

        var gaps = ImmutableArray.CreateBuilder<DigestionDispositionGap>();
        foreach (var rawGap in List(
                     raw,
                     "gaps",
                     $"entry {atomId} cover_disposition gaps must be a list"))
        {
            var gap = Mapping(rawGap, $"entry {atomId} cover_disposition gap must be a mapping");
            ExactKeys(gap, ["code", "detail"], $"entry {atomId} cover_disposition gap");
            gaps.Add(new DigestionDispositionGap(
                Scalar(gap, "code", $"entry {atomId} cover_disposition gap code"),
                Scalar(gap, "detail", $"entry {atomId} cover_disposition gap detail")));
        }

        var orderedGaps = gaps
            .OrderBy(static gap => gap.Code, StringComparer.Ordinal)
            .ThenBy(static gap => gap.Detail, StringComparer.Ordinal)
            .ToImmutableArray();
        if (!gaps.SequenceEqual(orderedGaps))
        {
            throw new FormatException(
                $"entry {atomId} cover_disposition gaps must use canonical ordinal ordering");
        }

        var timestamp = Scalar(
            raw,
            "recorded_at_utc",
            $"entry {atomId} cover_disposition recorded_at_utc");
        if (!DateTimeOffset.TryParseExact(
                timestamp,
                "O",
                CultureInfo.InvariantCulture,
                DateTimeStyles.RoundtripKind,
                out var recordedAtUtc)
            || recordedAtUtc.Offset != TimeSpan.Zero
            || !string.Equals(
                timestamp,
                recordedAtUtc.ToString("O", CultureInfo.InvariantCulture),
                StringComparison.Ordinal))
        {
            throw new FormatException(
                $"entry {atomId} cover_disposition recorded_at_utc must be canonical UTC round-trip time");
        }

        return new DigestionCoverDisposition(outcome, gids, orderedGaps, recordedAtUtc);
    }

    private static DigestionMigrationState ParseMigration(string value) => value switch
    {
        "residual" => DigestionMigrationState.Residual,
        "partial" => DigestionMigrationState.Partial,
        "absorbed" => DigestionMigrationState.Absorbed,
        _ => throw new FormatException($"invalid digestion migration status: {value}"),
    };

    private static DigestionTruthState ParseTruth(string value) => value switch
    {
        "closed" => DigestionTruthState.Closed,
        "tail" => DigestionTruthState.Tail,
        "open" => DigestionTruthState.Open,
        _ => throw new FormatException($"invalid digestion truth status: {value}"),
    };

    private static Dictionary<string, object?> Mapping(object? value, string message) =>
        value as Dictionary<string, object?> ?? throw new FormatException(message);

    private static List<object?> List(
        IReadOnlyDictionary<string, object?> mapping,
        string key,
        string message) =>
        mapping.GetValueOrDefault(key) as List<object?> ?? throw new FormatException(message);

    private static string Scalar(
        IReadOnlyDictionary<string, object?> mapping,
        string key,
        string context) =>
        mapping.GetValueOrDefault(key) is string value && !string.IsNullOrWhiteSpace(value)
            ? value
            : throw new FormatException($"{context} must be a nonempty scalar");

    private static int Integer(
        IReadOnlyDictionary<string, object?> mapping,
        string key,
        string context) =>
        mapping.GetValueOrDefault(key) is int value
            ? value
            : throw new FormatException($"{context} must be a nonnegative integer");

    private static ImmutableArray<string> Strings(List<object?> values, string context)
    {
        var builder = ImmutableArray.CreateBuilder<string>();
        foreach (var raw in values)
        {
            if (raw is not string value || string.IsNullOrWhiteSpace(value))
            {
                throw new FormatException($"{context} must contain nonempty scalars");
            }

            builder.Add(value);
        }

        return builder.ToImmutable();
    }

    private static void ExactKeys(
        IReadOnlyDictionary<string, object?> mapping,
        IReadOnlyCollection<string> expected,
        string context)
    {
        if (!mapping.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(expected))
        {
            throw new FormatException($"{context} keys are not canonical");
        }
    }

    // 必需键必须全在;可选键可有可无,但除此以外一个多余键都不许有。
    private static void ExactKeys(
        IReadOnlyDictionary<string, object?> mapping,
        IReadOnlyCollection<string> required,
        IReadOnlyCollection<string> optional,
        string context)
    {
        var keys = mapping.Keys.ToHashSet(StringComparer.Ordinal);
        if (!keys.IsSupersetOf(required)
            || !keys.IsSubsetOf(required.Concat(optional).ToHashSet(StringComparer.Ordinal)))
        {
            throw new FormatException($"{context} keys are not canonical");
        }
    }
}

internal static partial class BackfillInventoryLoader
{
    private const string LegacyStorageMessage =
        "legacy digestion ledger is unsupported; migrate to directory storage";

    internal const string RelativePath = "Meta/BACKFILL.yaml";
    internal const int SchemaVersion = 3;
    internal const string LedgerName = "theory-digestion-v1";
    private static readonly Regex TaskDeclarationPattern = new(
        "TASK (?<case>D5-T[0-9]{4})",
        RegexOptions.CultureInvariant);

    // 一原子一文件的消化台账落位;路径形状由 loader 闭世界识别。
    internal const string RootPath = "Meta/Digestion/backfill/";

    internal static bool IsCanonicalPath(string path)
    {
        if (!path.StartsWith(RootPath, StringComparison.Ordinal)) return false;
        var parts = path[RootPath.Length..].Split('/');
        if (parts.Length == 2 && parts[1] == "source.toml") return true;
        if (parts.Length != 3 || !parts[2].EndsWith(".yaml", StringComparison.Ordinal)) return false;
        var state = parts[1].Split('-');
        return state.Length == 2
            && state[0] is "residual" or "partial" or "absorbed"
            && state[1] is "closed" or "tail" or "open";
    }

    internal static BackfillInventoryDocument Load(RepositorySnapshot snapshot) =>
        LoadSnapshot(snapshot, LoadCandidateDirectorySnapshot);

    internal static BackfillInventoryDocument Load(
        RepositorySnapshot snapshot,
        DigestionEvaluationScope scope,
        RawChangeSet changes)
    {
        ArgumentNullException.ThrowIfNull(changes);
        var canonicalEncodingChanges = DigestionEvaluationScopes.ResolveChanges(scope, changes);
        return LoadSnapshot(
            snapshot,
            candidate => LoadCandidateDirectorySnapshot(candidate, canonicalEncodingChanges));
    }

    internal static BackfillInventoryDocument LoadBaseline(RepositorySnapshot snapshot) =>
        LoadSnapshot(snapshot, LoadBaselineDirectorySnapshot);

    internal static BackfillInventoryDocument LoadCandidateDelta(
        RepositorySnapshot candidate,
        RepositorySnapshot baseline,
        RawChangeSet changes)
    {
        ArgumentNullException.ThrowIfNull(candidate);
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(changes);

        var changed = changes.Paths
            .Select(static path => path.Value)
            .ToHashSet(StringComparer.Ordinal);
        var entries = new Dictionary<string, RawRepositoryEntry>(StringComparer.Ordinal);
        foreach (var (path, file) in candidate.Files)
        {
            entries[path.Value] = new RawRepositoryEntry(
                path.Value,
                file.RawBytes,
                file.GitBlobOid);
        }

        // Candidate-side parsing is authoritative only for the declared delta. For every
        // unchanged backfill record, feed the trusted baseline bytes to the strict loader.
        // This keeps historical projection quirks out of the candidate comparison while
        // retaining the current tree for all query inputs (Lean, targets, and source files).
        foreach (var (path, file) in baseline.Files
                     .Where(static pair => IsCanonicalPath(pair.Key.Value))
                     .Where(pair => !changed.Contains(pair.Key.Value)))
        {
            entries[path.Value] = new RawRepositoryEntry(
                path.Value,
                file.RawBytes,
                file.GitBlobOid);
        }

        var decoded = SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries.Values));
        return decoded switch
        {
            SnapshotDecodeOutcome.Decoded decodedSnapshot => LoadSnapshot(
                decodedSnapshot.Snapshot,
                snapshot => LoadCandidateDeltaDirectorySnapshot(snapshot, changed)),
            SnapshotDecodeOutcome.InfrastructureFailure failure => throw new FormatException(failure.Message),
        };
    }

    private static BackfillInventoryDocument LoadSnapshot(
        RepositorySnapshot snapshot,
        Func<RepositorySnapshot, BackfillInventoryDocument> loadDirectory)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        if (snapshot.TryGetFile(RelativePath, out _))
        {
            throw new FormatException(LegacyStorageMessage);
        }

        var canonicalDirectoryPaths = snapshot.Files.Keys
            .Where(path => IsCanonicalPath(path.Value))
            .ToArray();
        var hasDirectory = canonicalDirectoryPaths.Length > 0;

        if (!hasDirectory)
        {
            throw new FormatException("required governance document is missing");
        }

        foreach (var path in snapshot.Files.Keys
                     .Where(static path => path.Value.StartsWith(RootPath, StringComparison.Ordinal)))
        {
            if (!IsCanonicalPath(path.Value))
            {
                throw new FormatException($"noncanonical digestion ledger path: {path.Value}");
            }
        }

        var directoryDocument = loadDirectory(snapshot);
        ValidateQuarantineMachineFormMarkers(snapshot, directoryDocument);
        return directoryDocument;
    }

    internal static BackfillInventoryDocument LoadRoot(string repositoryRoot)
        => LoadRoot(repositoryRoot, trustedHistory: false);

    internal static BackfillInventoryDocument LoadTrustedRoot(string repositoryRoot)
        => LoadRoot(repositoryRoot, trustedHistory: true);

    private static BackfillInventoryDocument LoadRoot(
        string repositoryRoot,
        bool trustedHistory)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var root = Path.GetFullPath(repositoryRoot);
        var legacyPath = Path.Combine(
            root,
            RelativePath.Replace('/', Path.DirectorySeparatorChar));
        var directoryPath = Path.Combine(
            root,
            RootPath.Replace('/', Path.DirectorySeparatorChar));
        var hasLegacy = File.Exists(legacyPath);
        if (hasLegacy)
        {
            throw new FormatException(LegacyStorageMessage);
        }

        var hasDirectory = Directory.Exists(directoryPath)
            && Directory.EnumerateFiles(directoryPath, "*", SearchOption.AllDirectories)
                .Select(path => Path.GetRelativePath(root, path)
                    .Replace(Path.DirectorySeparatorChar, '/'))
                .Any(IsCanonicalPath);
        return hasDirectory
            ? LoadDirectory(repositoryRoot, trustedHistory)
            : throw new FormatException("required governance document is missing");
    }

    internal static BackfillInventoryDocument LoadDirectory(string repositoryRoot)
        => LoadDirectory(repositoryRoot, trustedHistory: false);

    private static BackfillInventoryDocument LoadDirectory(
        string repositoryRoot,
        bool trustedHistory)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var root = Path.GetFullPath(repositoryRoot);
        var directory = Path.Combine(root, RootPath.Replace('/', Path.DirectorySeparatorChar));
        var paths = Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
            .Concat(EnumerateD5LeanPaths(root))
            .Concat(EnumerateFormalizationReceiptPaths(root));
        return LoadRootSnapshot(root, paths, trustedHistory);
    }

    private static BackfillInventoryDocument LoadRootSnapshot(
        string root,
        IEnumerable<string> paths,
        bool trustedHistory)
    {
        var raw = RawRepositorySnapshot.Create(paths.Select(path => new RawRepositoryEntry(
            Path.GetRelativePath(root, path).Replace(Path.DirectorySeparatorChar, '/'),
            ImmutableArray.CreateRange(File.ReadAllBytes(path)))));
        return SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => trustedHistory
                ? LoadBaseline(decoded.Snapshot)
                : Load(decoded.Snapshot),
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new FormatException(failure.Message),
        };
    }

    private static BackfillInventoryDocument LoadCandidateDirectorySnapshot(
        RepositorySnapshot snapshot) =>
        LoadDirectorySnapshot(
            snapshot,
            static (text, path) => ParseCandidateSourceMetadata(text, path));

    private static BackfillInventoryDocument LoadCandidateDirectorySnapshot(
        RepositorySnapshot snapshot,
        RawChangeSet? canonicalEncodingChanges) =>
        LoadDirectorySnapshot(
            snapshot,
            (text, path) => ParseCandidateSourceMetadata(text, path, canonicalEncodingChanges));

    private static BackfillInventoryDocument LoadBaselineDirectorySnapshot(
        RepositorySnapshot snapshot) =>
        LoadDirectorySnapshot(
            snapshot,
            ParseBaselineSourceMetadata,
            static _ => true);

    private static BackfillInventoryDocument LoadCandidateDeltaDirectorySnapshot(
        RepositorySnapshot snapshot,
        IReadOnlySet<string> changed) =>
        LoadDirectorySnapshot(
            snapshot,
            static (text, path) => ParseCandidateSourceMetadata(text, path),
            path => !changed.Contains(path));

    private static BackfillInventoryDocument LoadDirectorySnapshot(
        RepositorySnapshot snapshot,
        Func<string, string, ParsedSourceMetadata> parseSourceMetadata,
        Func<string, bool>? allowLegacyCoverageReceipt = null)
    {
        var metadata = snapshot.Files
            .Where(static pair => pair.Key.Value.StartsWith(RootPath, StringComparison.Ordinal)
                && pair.Key.Value.EndsWith("/source.toml", StringComparison.Ordinal))
            .OrderBy(static pair => pair.Key.Value, StringComparer.Ordinal)
            .ToArray();
        if (metadata.Length == 0)
        {
            throw new FormatException($"digestion backfill directory is missing: {RootPath}");
        }

        var sources = ImmutableArray.CreateBuilder<DigestionLedgerSource>();
        foreach (var (metadataPath, metadataFile) in metadata)
        {
            var sourceRoot = metadataPath.Value[..^"source.toml".Length];
            var metadataParse = parseSourceMetadata(
                metadataFile.Text,
                metadataPath.Value);
            var fields = metadataParse.Fields;
            var sourceId = fields["source_id"].Single();
            if (!string.Equals(sourceRoot, $"{RootPath}{sourceId}/", StringComparison.Ordinal))
            {
                throw new FormatException($"source metadata path disagrees with source_id: {metadataPath.Value}");
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
                if (YamlSubsetParser.Parse(file.Text) is not Dictionary<string, object?> entry)
                {
                    throw new FormatException($"backfill atom must be a mapping: {path.Value}");
                }

                var atomId = suffix[(slash + 1)..^".yaml".Length];
                if (!entry.TryAdd("atom_id", atomId) || !entry.TryAdd("status", new Dictionary<string, object?>(StringComparer.Ordinal)
                    {
                        ["migration"] = state[0],
                        ["truth"] = state[1],
                    }))
                {
                    throw new FormatException($"backfill atom contains path-derived fields: {path.Value}");
                }

                var parsedEntry = BackfillInventoryDocument.ParseEntry(
                    sourceId,
                    fields["path"].Single(),
                    fields["atomizer"].Single(),
                    entry,
                    allowLegacyCoverageReceipt?.Invoke(path.Value) ?? false);
                entries.Add(parsedEntry);
            }

            var parsedSource = new DigestionLedgerSource(
                sourceId,
                fields["path"].Single(),
                fields["atomizer"].Single(),
                fields.GetValueOrDefault("acknowledged_stale", []).ToImmutableArray(),
                metadataParse.GenreRegistryProjection,
                entries.ToImmutable());
            sources.Add(parsedSource);
        }

        var sourceRoots = metadata
            .Select(static pair => pair.Key.Value[..^"source.toml".Length])
            .ToArray();
        foreach (var atomPath in snapshot.Files.Keys
                     .Where(static path => path.Value.StartsWith(RootPath, StringComparison.Ordinal)
                         && path.Value.EndsWith(".yaml", StringComparison.Ordinal)))
        {
            if (sourceRoots.Count(root => atomPath.Value.StartsWith(root, StringComparison.Ordinal)) != 1)
            {
                throw new FormatException(
                    $"backfill atom is not owned by exactly one source: {atomPath.Value}");
            }
        }

        return BackfillInventoryDocument.Create(sources.ToImmutable(), DeriveTickets(snapshot));
    }

    internal static ImmutableArray<BackfillTicketReference> DeriveTickets(
        RepositorySnapshot snapshot)
    {
        var modulesByCase = new SortedDictionary<string, string>(StringComparer.Ordinal);
        foreach (var (path, file) in snapshot.Files
                     .Where(static pair => pair.Key.Value.StartsWith("D5/", StringComparison.Ordinal)
                         && pair.Key.Value.EndsWith(".lean", StringComparison.Ordinal))
                     .OrderBy(static pair => pair.Key.Value, StringComparer.Ordinal))
        {
            var module = path.Value[..^".lean".Length];
            foreach (Match match in TaskDeclarationPattern.Matches(file.Text))
            {
                var caseId = match.Groups["case"].Value;
                if (modulesByCase.TryGetValue(caseId, out var existingModule)
                    && !string.Equals(existingModule, module, StringComparison.Ordinal))
                {
                    throw new FormatException(
                        $"TASK case {caseId} is declared by multiple D5 Lean modules: "
                        + $"{existingModule}, {module}");
                }

                modulesByCase.TryAdd(caseId, module);
            }
        }

        return modulesByCase
            .Select(static pair => new BackfillTicketReference(pair.Key, pair.Value))
            .ToImmutableArray();
    }

    private static IEnumerable<string> EnumerateD5LeanPaths(string root)
    {
        var d5Root = Path.Combine(root, "D5");
        return Directory.Exists(d5Root)
            ? Directory.EnumerateFiles(d5Root, "*.lean", SearchOption.AllDirectories)
            : [];
    }

}
