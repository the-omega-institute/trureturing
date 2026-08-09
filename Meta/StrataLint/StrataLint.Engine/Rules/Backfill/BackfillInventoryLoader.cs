using System.Collections.Immutable;

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
    private readonly ImmutableArray<BackfillTicketReference> projectedTickets;
    private readonly ImmutableArray<DigestionLedgerSource> projectedSources;
    private readonly ImmutableArray<BackfillReceiptSyntax> receiptSyntaxes;

    internal BackfillInventoryDocument(
        IReadOnlyDictionary<string, object?> root,
        ImmutableArray<BackfillReceiptSyntax> receiptSyntaxes)
        : this(root, default, default, receiptSyntaxes)
    {
    }

    private BackfillInventoryDocument(
        IReadOnlyDictionary<string, object?> root,
        ImmutableArray<BackfillTicketReference> projectedTickets,
        ImmutableArray<DigestionLedgerSource> projectedSources,
        ImmutableArray<BackfillReceiptSyntax> receiptSyntaxes)
    {
        this.root = root;
        this.projectedTickets = projectedTickets;
        this.projectedSources = projectedSources;
        this.receiptSyntaxes = receiptSyntaxes;
    }

    internal IReadOnlyDictionary<string, object?> Root => root;

    internal static BackfillInventoryDocument Create(
        ImmutableArray<DigestionLedgerSource> sources,
        ImmutableArray<BackfillTicketReference> tickets)
    {
        var ticketIndex = tickets.Select(static ticket => (object?)new Dictionary<string, object?>(StringComparer.Ordinal)
        {
            ["case_id"] = ticket.CaseId,
            ["gid"] = ticket.Gid,
        }).ToList();
        var root = new Dictionary<string, object?>(StringComparer.Ordinal)
        {
            ["schema_version"] = BackfillInventoryLoader.SchemaVersion,
            ["ledger"] = BackfillInventoryLoader.LedgerName,
            ["sources"] = new List<object?>(),
            ["ticket_index"] = ticketIndex,
        };
        return new BackfillInventoryDocument(root, tickets, sources, []);
    }

    internal ImmutableArray<BackfillTicketReference> RequireTickets()
    {
        if (!projectedTickets.IsDefault)
        {
            return projectedTickets;
        }

        var ticketIndex = List(root, "ticket_index", "ticket_index must be a list");
        var tickets = ImmutableArray.CreateBuilder<BackfillTicketReference>();
        foreach (var rawTicket in ticketIndex)
        {
            var ticket = Mapping(rawTicket, "ticket_index entries must be mappings");
            ExactKeys(ticket, ["case_id", "gid"], "ticket_index entry");
            tickets.Add(new BackfillTicketReference(
                Scalar(ticket, "case_id", "ticket_index case_id"),
                Scalar(ticket, "gid", "ticket_index gid")));
        }

        return tickets.ToImmutable();
    }

    internal ImmutableArray<DigestionLedgerSource> RequireDigestionSources()
    {
        if (!projectedSources.IsDefault)
        {
            return projectedSources;
        }

        var rawSources = List(root, "sources", "sources must be a list");
        var sources = ImmutableArray.CreateBuilder<DigestionLedgerSource>();
        var receiptIndex = 0;
        foreach (var rawSource in rawSources)
        {
            var source = Mapping(rawSource, "sources must contain mappings");
            ExactKeys(
                source,
                source.ContainsKey("acknowledged_stale")
                    ? ["source_id", "path", "atomizer", "acknowledged_stale", "entries"]
                    : ["source_id", "path", "atomizer", "entries"],
                "source");
            var sourceId = Scalar(source, "source_id", "source_id");
            var sourcePath = Scalar(source, "path", $"source {sourceId} path");
            var atomizer = Scalar(source, "atomizer", $"source {sourceId} atomizer");
            var acknowledgedStale = source.ContainsKey("acknowledged_stale")
                ? Strings(
                    List(source, "acknowledged_stale", $"source {sourceId} acknowledged_stale must be a list"),
                    $"source {sourceId} acknowledged_stale")
                : ImmutableArray<string>.Empty;
            var entries = ImmutableArray.CreateBuilder<DigestionLedgerEntry>();
            foreach (var rawEntry in List(source, "entries", $"source {sourceId} entries must be a list"))
            {
                if (receiptIndex >= receiptSyntaxes.Length)
                {
                    throw new FormatException("BACKFILL receipt preimage count is incomplete");
                }

                entries.Add(ParseEntry(
                    sourceId,
                    sourcePath,
                    atomizer,
                    rawEntry,
                    receiptSyntaxes[receiptIndex++]));
            }

            sources.Add(new DigestionLedgerSource(
                sourceId,
                sourcePath,
                atomizer,
                acknowledgedStale,
                entries.ToImmutable()));
        }

        if (receiptIndex != receiptSyntaxes.Length)
        {
            throw new FormatException("BACKFILL receipt preimage count exceeds parsed entries");
        }

        return sources.ToImmutable();
    }

    internal ImmutableArray<DigestionLedgerEntry> RequireDigestionEntries() =>
        RequireDigestionSources().SelectMany(static source => source.Entries).ToImmutableArray();

    internal BackfillInventoryDocument WithDigestionSources(
        ImmutableArray<DigestionLedgerSource> sources) =>
        new(root, RequireTickets(), sources, receiptSyntaxes);

    internal BackfillInventoryDocument WithTickets(
        ImmutableArray<BackfillTicketReference> tickets) =>
        new(root, tickets, RequireDigestionSources(), receiptSyntaxes);

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
        BackfillReceiptSyntax? receiptSyntax)
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
            receiptSyntax,
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
            ["chain_atoms", "tail_authorization"],
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
            tailAuthorization);
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

internal static class BackfillInventoryLoader
{
    private const string CoexistingStorageMessage =
        "legacy and directory digestion ledgers cannot coexist";

    internal const string RelativePath = "Meta/BACKFILL.yaml";
    internal const int SchemaVersion = 3;
    internal const string LedgerName = "theory-digestion-v1";

    // 一原子一文件的消化台账落位。这三个成员先行加入 base 侧,使后续迁移 PR 的
    // baseline admission 能识别 Meta/Digestion/backfill/** —— 否则「要认识这片路径
    // 才能往里放文件,而放文件那次 PR 的法官还不认识它」形成引导死结。
    // 今天树里还没有这些路径,故本谓词对当前 dev 恒为 false。
    internal const string RootPath = "Meta/Digestion/backfill/";
    internal const string TicketIndexPath = "Meta/Digestion/ticket-index.toml";

    internal static bool IsCanonicalPath(string path)
    {
        if (string.Equals(path, TicketIndexPath, StringComparison.Ordinal)) return true;
        if (!path.StartsWith(RootPath, StringComparison.Ordinal)) return false;
        var parts = path[RootPath.Length..].Split('/');
        if (parts.Length == 2 && parts[1] == "source.toml") return true;
        if (parts.Length != 3 || !parts[2].EndsWith(".yaml", StringComparison.Ordinal)) return false;
        var state = parts[1].Split('-');
        return state.Length == 2
            && state[0] is "residual" or "partial" or "absorbed"
            && state[1] is "closed" or "tail" or "open";
    }

    internal static BackfillInventoryDocument Load(string text)
    {
        if (YamlSubsetParser.Parse(text) is not Dictionary<string, object?> root)
        {
            throw new FormatException("BACKFILL top-level YAML value must be a mapping");
        }

        if (root.GetValueOrDefault("schema_version") is not int version || version != SchemaVersion)
        {
            throw new FormatException($"BACKFILL must use schema_version {SchemaVersion}; legacy schemas are not read");
        }

        if (root.GetValueOrDefault("ledger") is not string ledger
            || !string.Equals(ledger, LedgerName, StringComparison.Ordinal))
        {
            throw new FormatException($"BACKFILL ledger must be {LedgerName}");
        }

        return new BackfillInventoryDocument(root, BackfillReceiptPreimage.Extract(text));
    }

    internal static BackfillInventoryDocument Load(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        var hasLegacy = snapshot.TryGetFile(RelativePath, out var legacyFile);
        var canonicalDirectoryPaths = snapshot.Files.Keys
            .Where(path => IsCanonicalPath(path.Value))
            .ToArray();
        var hasDirectory = canonicalDirectoryPaths.Length > 0;

        if (hasLegacy && hasDirectory)
        {
            throw new FormatException(CoexistingStorageMessage);
        }

        if (hasLegacy)
        {
            return Load(legacyFile!.Text);
        }

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

        return LoadDirectorySnapshot(snapshot);
    }

    // 磁盘树的双形态入口:与 Load(RepositorySnapshot) 同语义——旧单文件与新目录
    // 台账二选一;两形态并存由快照路径 Load(RepositorySnapshot) 在规则层拒绝。
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
        var ticketIndexPath = Path.Combine(
            root,
            TicketIndexPath.Replace('/', Path.DirectorySeparatorChar));
        var hasLegacy = File.Exists(legacyPath);
        var hasDirectory = File.Exists(ticketIndexPath)
            || Directory.Exists(directoryPath)
            && Directory.EnumerateFiles(directoryPath, "*", SearchOption.AllDirectories)
                .Select(path => Path.GetRelativePath(root, path)
                    .Replace(Path.DirectorySeparatorChar, '/'))
                .Any(IsCanonicalPath);
        if (hasLegacy && hasDirectory)
        {
            throw new FormatException(CoexistingStorageMessage);
        }

        return hasLegacy
            ? Load(File.ReadAllText(legacyPath))
            : LoadDirectory(repositoryRoot);
    }

    internal static BackfillInventoryDocument LoadDirectory(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var root = Path.GetFullPath(repositoryRoot);
        var directory = Path.Combine(root, RootPath.Replace('/', Path.DirectorySeparatorChar));
        var paths = Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
            .Append(Path.Combine(root, TicketIndexPath.Replace('/', Path.DirectorySeparatorChar)));
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

    private static BackfillInventoryDocument LoadDirectorySnapshot(RepositorySnapshot snapshot)
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
            var fields = ParseSourceMetadata(metadataFile.Text, metadataPath.Value);
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

                entries.Add(BackfillInventoryDocument.ParseEntry(
                    sourceId,
                    fields["path"].Single(),
                    fields["atomizer"].Single(),
                    entry,
                    null));
            }

            sources.Add(new DigestionLedgerSource(
                sourceId,
                fields["path"].Single(),
                fields["atomizer"].Single(),
                fields.GetValueOrDefault("acknowledged_stale", []).ToImmutableArray(),
                entries.ToImmutable()));
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

        var tickets = snapshot.TryGetFile(TicketIndexPath, out var ticketFile)
            ? ParseTickets(ticketFile.Text)
            : throw new FormatException($"digestion ticket index is missing: {TicketIndexPath}");
        return BackfillInventoryDocument.Create(sources.ToImmutable(), tickets);
    }

    private static Dictionary<string, List<string>> ParseSourceMetadata(string text, string path)
    {
        var result = new Dictionary<string, List<string>>(StringComparer.Ordinal);
        foreach (var rawLine in text.Split('\n', StringSplitOptions.RemoveEmptyEntries))
        {
            var split = rawLine.Split(" = ", 2, StringSplitOptions.None);
            if (split.Length != 2)
            {
                throw new FormatException($"invalid source metadata: {path}");
            }

            List<string> values;
            try
            {
                values = ParseTomlValues(split[1]);
            }
            catch (FormatException) when (split[0] is "source_id" or "path" or "atomizer")
            {
                throw new FormatException(
                    $"source metadata identity fields must be single quoted strings: {path}");
            }

            if (split[0] is "source_id" or "path" or "atomizer"
                && split[1].StartsWith('['))
            {
                throw new FormatException(
                    $"source metadata identity fields must be single quoted strings: {path}");
            }

            if (split[0] == "acknowledged_stale"
                && (!split[1].StartsWith('[')
                    || !split[1].EndsWith(']')
                    || values.Any(string.IsNullOrWhiteSpace)))
            {
                throw new FormatException(
                    $"acknowledged_stale must be a quoted string array without blank elements: {path}");
            }

            if (!result.TryAdd(split[0], values))
            {
                throw new FormatException($"invalid source metadata: {path}");
            }
        }

        if (!result.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(
                result.ContainsKey("acknowledged_stale")
                    ? ["source_id", "path", "atomizer", "acknowledged_stale"]
                    : ["source_id", "path", "atomizer"]))
        {
            throw new FormatException($"source metadata keys are not canonical: {path}");
        }


        if (result["source_id"].Count != 1
            || result["path"].Count != 1
            || result["atomizer"].Count != 1
            || string.IsNullOrWhiteSpace(result["source_id"][0])
            || string.IsNullOrWhiteSpace(result["path"][0])
            || string.IsNullOrWhiteSpace(result["atomizer"][0]))
        {
            throw new FormatException(
                $"source metadata identity fields must be single quoted strings: {path}");
        }

        return result;
    }

    private static List<string> ParseTomlValues(string encoded)
    {
        if (encoded.StartsWith('[') || encoded.EndsWith(']'))
        {
            if (!encoded.StartsWith('[') || !encoded.EndsWith(']'))
            {
                throw new FormatException("source metadata values must be quoted strings");
            }

            var body = encoded[1..^1];
            if (body.Length == 0) return [];
            return body.Split(", ", StringSplitOptions.None)
                .Select(ParseQuotedTomlScalar)
                .ToList();
        }

        return [ParseQuotedTomlScalar(encoded)];
    }

    private static string ParseQuotedTomlScalar(string encoded)
    {
        if (encoded.Length < 2
            || encoded[0] != '"'
            || encoded[^1] != '"'
            || encoded.AsSpan(1, encoded.Length - 2).Contains('"'))
        {
            throw new FormatException("source metadata values must be quoted strings");
        }

        return encoded[1..^1];
    }

    internal static ImmutableArray<BackfillTicketReference> ParseTickets(string text)
    {
        var tickets = ImmutableArray.CreateBuilder<BackfillTicketReference>();
        foreach (var line in text.Split('\n', StringSplitOptions.RemoveEmptyEntries))
        {
            var parts = line.Split(" = ", 2, StringSplitOptions.None);
            if (parts.Length != 2)
            {
                throw new FormatException("invalid digestion ticket index");
            }

            List<string> values;
            try
            {
                values = ParseTomlValues(parts[1]);
            }
            catch (FormatException)
            {
                throw new FormatException("invalid digestion ticket index");
            }

            if (values.Count != 1)
            {
                throw new FormatException("invalid digestion ticket index");
            }

            tickets.Add(new BackfillTicketReference(parts[0], values[0]));
        }

        return tickets.ToImmutable();
    }
}
