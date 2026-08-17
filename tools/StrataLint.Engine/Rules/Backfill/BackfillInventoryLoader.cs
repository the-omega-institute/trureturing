using System.Collections.Immutable;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal sealed class BackfillInventoryDocument
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
        object? rawEntry)
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
        var receipts = ParseReceipts(atomId, entry.GetValueOrDefault("receipts"));
        if (receipts.Quarantine is not null && coverageGids.Length > 0)
        {
            throw new FormatException(
                $"entry {atomId} cannot be quarantined because coverage_gids provides a machine-form statement");
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

    private static DigestionReceipts ParseReceipts(string atomId, object? rawReceipts)
    {
        var receipts = Mapping(rawReceipts, $"entry {atomId} receipts must be a mapping");

        // chain_atoms 与 tail_authorization 降为**可选键**:一节点一文件的目录形态不再写出
        // 它们(实测 dev 现有 2,030 条记录里 100% 为 `[]` 与 `null`)。
        // 但**在场时校验一字不减** —— tail_authorization 是活的能力(absorbed-tail 授权删除,
        // 见 DigestionLedgerTests 的 ArbitraryHashedRepositoryFileCannotAuthorizeTailDeletion),
        // 只是尚无实例;把「当前没有实例」当成「机制已死」会削掉一条真能力。
        ExactKeys(
            receipts,
            ["coverage", "scribe", "unresolved_subitems"],
            ["chain_atoms", "tail_authorization", "quarantine"],
            $"entry {atomId} receipts");
        var coverage = ImmutableArray.CreateBuilder<DigestionCoverageReceipt>();
        foreach (var rawCoverage in List(receipts, "coverage", $"entry {atomId} coverage receipts must be a list"))
        {
            var item = Mapping(rawCoverage, $"entry {atomId} coverage receipt must be a mapping");
            ExactKeys(item, ["gid", "source_sha256", "target_sha256"], $"entry {atomId} coverage receipt");
            coverage.Add(new DigestionCoverageReceipt(
                Scalar(item, "gid", $"entry {atomId} coverage gid"),
                Scalar(item, "source_sha256", $"entry {atomId} coverage source_sha256"),
                Scalar(item, "target_sha256", $"entry {atomId} coverage target_sha256")));
        }

        var scribe = ImmutableArray.CreateBuilder<DigestionScribeReceipt>();
        foreach (var rawScribe in List(receipts, "scribe", $"entry {atomId} scribe receipts must be a list"))
        {
            var item = Mapping(rawScribe, $"entry {atomId} scribe receipt must be a mapping");
            ExactKeys(item, ["gid", "definition_sha256", "emission_sha256"], $"entry {atomId} scribe receipt");
            scribe.Add(new DigestionScribeReceipt(
                Scalar(item, "gid", $"entry {atomId} scribe gid"),
                Scalar(item, "definition_sha256", $"entry {atomId} definition_sha256"),
                Scalar(item, "emission_sha256", $"entry {atomId} emission_sha256")));
        }

        DigestionExternalReceipt? tailAuthorization = null;
        if (receipts.GetValueOrDefault("tail_authorization") is { } rawTail)
        {
            var tail = Mapping(rawTail, $"entry {atomId} tail_authorization must be null or a mapping");
            ExactKeys(tail, ["path", "sha256"], $"entry {atomId} tail_authorization");
            tailAuthorization = new DigestionExternalReceipt(
                Scalar(tail, "path", $"entry {atomId} tail authorization path"),
                Scalar(tail, "sha256", $"entry {atomId} tail authorization sha256"));
        }

        DigestionQuarantine? quarantine = null;
        if (receipts.ContainsKey("quarantine"))
        {
            var rawQuarantine = Mapping(
                receipts.GetValueOrDefault("quarantine"),
                $"entry {atomId} quarantine must be a mapping");
            if (!rawQuarantine.ContainsKey("justification"))
            {
                throw new FormatException(
                    $"entry {atomId} quarantine justification is required");
            }

            if (!rawQuarantine.ContainsKey("reentry_condition"))
            {
                throw new FormatException(
                    $"entry {atomId} quarantine reentry_condition is required");
            }

            ExactKeys(
                rawQuarantine,
                ["justification", "reentry_condition"],
                $"entry {atomId} quarantine");
            quarantine = new DigestionQuarantine(
                Scalar(rawQuarantine, "justification", $"entry {atomId} quarantine justification"),
                Scalar(rawQuarantine, "reentry_condition", $"entry {atomId} quarantine reentry_condition"));
        }

        return new DigestionReceipts(
            coverage.ToImmutable(),
            scribe.ToImmutable(),
            Strings(
                List(receipts, "unresolved_subitems", $"entry {atomId} unresolved_subitems must be a list"),
                $"entry {atomId} unresolved_subitems"),
            receipts.ContainsKey("chain_atoms")
                ? Strings(
                    List(receipts, "chain_atoms", $"entry {atomId} chain_atoms must be a list"),
                    $"entry {atomId} chain_atoms")
                : [],
            tailAuthorization,
            quarantine);
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

    internal static BackfillInventoryDocument LoadBaseline(RepositorySnapshot snapshot) =>
        LoadSnapshot(snapshot, LoadBaselineDirectorySnapshot);

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
            ? LoadDirectory(repositoryRoot)
            : throw new FormatException("required governance document is missing");
    }

    internal static BackfillInventoryDocument LoadDirectory(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var root = Path.GetFullPath(repositoryRoot);
        var directory = Path.Combine(root, RootPath.Replace('/', Path.DirectorySeparatorChar));
        var paths = Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
            .Concat(EnumerateD5LeanPaths(root))
            .Concat(EnumerateFormalizationReceiptPaths(root));
        return LoadRootSnapshot(root, paths);
    }

    private static BackfillInventoryDocument LoadRootSnapshot(
        string root,
        IEnumerable<string> paths)
    {
        var raw = RawRepositorySnapshot.Create(paths.Select(path => new RawRepositoryEntry(
            Path.GetRelativePath(root, path).Replace(Path.DirectorySeparatorChar, '/'),
            ImmutableArray.CreateRange(File.ReadAllBytes(path)))));
        return SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => Load(decoded.Snapshot),
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new FormatException(failure.Message),
        };
    }

    private static BackfillInventoryDocument LoadCandidateDirectorySnapshot(
        RepositorySnapshot snapshot) =>
        LoadDirectorySnapshot(snapshot, ParseCandidateSourceMetadata);

    private static BackfillInventoryDocument LoadBaselineDirectorySnapshot(
        RepositorySnapshot snapshot) =>
        LoadDirectorySnapshot(snapshot, ParseBaselineSourceMetadata);

    private static BackfillInventoryDocument LoadDirectorySnapshot(
        RepositorySnapshot snapshot,
        Func<string, string, ParsedSourceMetadata> parseSourceMetadata)
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
                    entry);
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
