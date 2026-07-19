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

    private static DigestionLedgerEntry ParseEntry(
        string sourceId,
        string sourcePath,
        string atomizer,
        object? rawEntry,
        BackfillReceiptSyntax receiptSyntax)
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
        ExactKeys(
            receipts,
            ["coverage", "scribe", "unresolved_subitems", "chain_atoms", "tail_authorization"],
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
            Strings(
                List(receipts, "chain_atoms", $"entry {atomId} chain_atoms must be a list"),
                $"entry {atomId} chain_atoms"),
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
}

internal static class BackfillInventoryLoader
{
    internal const string RelativePath = "Meta/BACKFILL.yaml";
    internal const int SchemaVersion = 3;
    internal const string LedgerName = "theory-digestion-v1";

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
}
