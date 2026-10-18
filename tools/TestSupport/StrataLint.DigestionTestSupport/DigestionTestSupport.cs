using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.TestSupport;

internal static class DigestionTestSupport
{
    internal static BackfillInventoryDocument EmptyDocument(string atomizerId) =>
        Document(atomizerId, []);

    internal static BackfillInventoryDocument Document(
        string atomizerId,
        ImmutableArray<DigestionLedgerEntry> entries,
        string sourceId = "source",
        string sourcePath = "docs/source.md",
        GenreRegistryCheck? genreRegistryCheck = null,
        ImmutableArray<string> acknowledgedStale = default,
        ImmutableArray<BackfillTicketReference> tickets = default) =>
        BackfillInventoryDocument.Create(
        [
            new DigestionLedgerSource(
                sourceId,
                sourcePath,
                atomizerId,
                acknowledgedStale.IsDefault ? [] : acknowledgedStale,
                GenreRegistryProjection.Available(
                    genreRegistryCheck ?? GenreRegistryCheck.NoGenreRegistry),
                entries),
        ],
        tickets.IsDefault ? [] : tickets);

    internal static DigestionLedgerEntry Entry(
        DigestionAtom atom,
        string atomId,
        string atomizerId,
        DigestionMigrationState migration = DigestionMigrationState.Residual,
        DigestionTruthState truth = DigestionTruthState.Open,
        ImmutableArray<string> coverageGids = default,
        DigestionReceipts? receipts = null,
        string sourceId = "source",
        string sourcePath = "docs/source.md",
        string? casRef = null) => new(
            sourceId,
            sourcePath,
            atomizerId,
            atomId,
            atom.Fingerprints,
            coverageGids.IsDefault
                ? []
                : coverageGids.Select(static gid => new DigestionCoverageEdge(gid, null))
                    .ToImmutableArray(),
            receipts ?? new DigestionReceipts([], [], null),
            new DigestionStatus(migration, truth),
            casRef ?? atom.Fingerprints.RawSha256);

    internal static string ReceiptList(string key, string value, int spaces) => value == "[]"
        ? new string(' ', spaces) + key + ": []"
        : new string(' ', spaces) + key + ":\n" + Indent(value, spaces + 2);

    private static string Indent(string value, int spaces) => string.Join(
        '\n',
        value.Split('\n').Select(line => new string(' ', spaces) + line));

    // Synthetic repositories declare their input policy explicitly, just as production does.
    internal static RawRepositorySnapshot WithSourcePolicy(RawRepositorySnapshot raw,
        IEnumerable<string>? sourcePatterns = null)
    {
        if (raw.Entries.Any(entry => entry.Path == FileMapLoader.RelativePath)) return raw;
        var files = (sourcePatterns ?? raw.Entries
                .Where(entry => !entry.Path.StartsWith("Meta/", StringComparison.Ordinal))
                .Select(entry => entry.Path)).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal)
            .Select(path => "{ pattern = " + System.Text.Json.JsonSerializer.Serialize(path)
                + ", kind = \"data\", admission_plane = \"content\", produced_by = \"none\", consumed_by = [\"reader\"], "
                + "verified_by = [\"SnapshotDecoder\"], artifact_id = \"none\", runtime_disposition = \"committed-source\", digestion_source = true }");
        var policy = "schema_version = 6\nfiles = [\n" + string.Join(",\n", files)
            + "\n]\n[evidence.artifact_kinds.md]\nprofile = \"opaque-text\"\nselectors = [\"result\"]\npath_selectors = [\"formal\"]\n[residence_policy]\ncase_id = \"TEST\"\ndesired = \"data-must-live-outside-tools\"\nknown_violation_count = 0\nstatus = \"closed\"\n";
        return RawRepositorySnapshot.Create(raw.Entries.Add(RawRepositoryEntry.FromText(
            FileMapLoader.RelativePath, policy)), raw.PathInventory);
    }

    internal static RepositorySnapshot Snapshot(params (string Path, byte[] Bytes)[] files)
    {
        var materialized = files.ToList();
        if (materialized.All(static file => file.Path != EngineeringRegistrationFixture.Path))
            materialized.Add((EngineeringRegistrationFixture.Path,
                System.Text.Encoding.UTF8.GetBytes(EngineeringRegistrationFixture.Manifest())));
        var raw = RawRepositorySnapshot.Create(materialized.Select(file => new RawRepositoryEntry(
            file.Path,
            ImmutableArray.CreateRange(file.Bytes))));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(DigestionTestSupport.WithSourcePolicy(raw))).Snapshot;
    }

    internal static RepositorySnapshot Snapshot(
        byte[] sourceBytes,
        IEnumerable<DigestionCasObject> casObjects) => Snapshot(
            casObjects
                .Select(static item => (item.RelativePath, item.Bytes.ToArray()))
                .Prepend(("docs/source.md", sourceBytes))
                .ToArray());

    internal static (string Path, byte[] Bytes) CasFile(DigestionAtom atom) =>
        (DigestionCasStore.RootPath + atom.Fingerprints.RawSha256["sha256:".Length..],
            atom.RawBytes.ToArray());

    internal static AcceptedLeanClosure AcceptedLean(params string[] paths) => AcceptedLean(
        paths.Select(path => (path, new LeanFileReport(
            ImmutableArray<string>.Empty,
            [new LeanDeclaration("probe", "theorem", "True", ImmutableArray<string>.Empty)]))).ToArray());

    internal static AcceptedLeanClosure AcceptedLean(
        params (string Path, LeanFileReport Report)[] reports) =>
        AcceptedLeanClosure.Create(LeanAxiomReport.Create(reports.ToDictionary(
            static item => item.Path,
            static item => item.Report,
            StringComparer.Ordinal)));

    internal static string Lean(string gid) => $$"""
        /- GID: {{gid}}
           generality: G
           mirror-B: none(waiver:test)
           mirror-E: none(waiver:test)
           anchors: []
           digest: Digestion test fixture. -/
        theorem probe : True := by trivial
        """;
}
