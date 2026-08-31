using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class DigestionTestSupport
{
    private static readonly Lazy<TheoryAtomizerRules> CanonicalRules = new(() =>
    {
        var root = AppContext.BaseDirectory;
        while (!File.Exists(Path.Combine(root, TheoryAtomizerDataLoader.DataPath)))
        {
            root = Directory.GetParent(root)?.FullName
                ?? throw new InvalidOperationException("repository root not found");
        }
        return TheoryAtomizerDataLoader.Load(Snapshot((
            TheoryAtomizerDataLoader.DataPath,
            File.ReadAllBytes(Path.Combine(root, TheoryAtomizerDataLoader.DataPath)))));
    });

    internal static TheoryAtomizerRules Rules => CanonicalRules.Value;

    internal static byte[] RulesBytes
    {
        get
        {
            var root = AppContext.BaseDirectory;
            while (!File.Exists(Path.Combine(root, TheoryAtomizerDataLoader.DataPath)))
            {
                root = Directory.GetParent(root)?.FullName
                    ?? throw new InvalidOperationException("repository root not found");
            }
            return File.ReadAllBytes(Path.Combine(root, TheoryAtomizerDataLoader.DataPath));
        }
    }

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
            coverageGids.IsDefault ? [] : coverageGids,
            receipts ?? new DigestionReceipts([], [], [], [], null),
            new DigestionStatus(migration, truth),
            casRef ?? atom.Fingerprints.RawSha256);

    internal static string ReceiptList(string key, string value, int spaces) => value == "[]"
        ? new string(' ', spaces) + key + ": []"
        : new string(' ', spaces) + key + ":\n" + Indent(value, spaces + 2);

    private static string Indent(string value, int spaces) => string.Join(
        '\n',
        value.Split('\n').Select(line => new string(' ', spaces) + line));

    internal static RepositorySnapshot Snapshot(params (string Path, byte[] Bytes)[] files)
    {
        var materialized = files.ToList();
        if (materialized.All(static file => file.Path != TheoryAtomizerDataLoader.DataPath))
        {
            materialized.Add((
                TheoryAtomizerDataLoader.DataPath,
                RulesBytes));
        }
        var raw = RawRepositorySnapshot.Create(materialized.Select(file => new RawRepositoryEntry(
            file.Path,
            ImmutableArray.CreateRange(file.Bytes))));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
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
