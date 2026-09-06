using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestScopeTests
{
    private const string AlphaPath = "docs/develop/theory/ALPHA.md";
    private const string BetaPath = "docs/develop/theory/BETA.md";
    private const string AlphaText = "## Claim 1\n\nAlpha fact.\n\n";
    private const string BetaText = "## Claim 2\n\nBeta fact.\n\n";
    private const string Addition = "## Claim 3\n\nAdditional fact.\n";
    private static readonly ImmutableHashSet<string> BetaOnly =
        ImmutableHashSet.Create(StringComparer.Ordinal, "beta");

    private static DigestionAtom Atom(string text) => Assert.Single(
        GenericAtomizer.Atomize(Encoding.UTF8.GetBytes(text), DigestionTestSupport.Rules).Claims);

    private static DigestionLedgerSource Source(string id, string path, string text, bool populated = true)
    {
        var atom = Atom(text);
        return new DigestionLedgerSource(id, path, AtomizerRegistry.GenericId, [],
            GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry),
            populated ? [DigestionTestSupport.Entry(atom, atom.Fingerprints.RawSha256[7..],
                AtomizerRegistry.GenericId, sourceId: id, sourcePath: path)] : []);
    }

    private static BackfillInventoryDocument Ledger(bool populated = true) =>
        BackfillInventoryDocument.Create([
            Source("alpha", AlphaPath, AlphaText, populated),
            Source("beta", BetaPath, BetaText, populated),
        ], []);

    private static RuleFixture Fixture(BackfillInventoryDocument? ledger = null,
        string alphaText = AlphaText, string betaText = BetaText)
    {
        ledger ??= Ledger();
        var fixture = new RuleFixture();
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files.Remove(RuleFixture.FixtureDigestionSourcePath);
            files.Remove(RuleFixture.FixtureCasPath);
            files[AlphaPath] = alphaText;
            files[BetaPath] = betaText;
            DirectoryLedgerTestSupport.ReplaceWithProjection(files, ledger);
            foreach (var text in new[] { alphaText, betaText })
            {
                var atom = Atom(text);
                if (ledger.RequireDigestionEntries().Any(entry => entry.CasRef == atom.Fingerprints.RawSha256))
                    AddCas(files, atom);
            }
        }
        return fixture;
    }

    private static void AddCas(IDictionary<string, string> files, DigestionAtom atom)
    {
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        files[captured.RelativePath] = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
    }

    private static RawRepositorySnapshot Raw(IReadOnlyDictionary<string, string> files) =>
        RawRepositorySnapshot.Create(files.Select(static item => RawRepositoryEntry.FromText(item.Key, item.Value)));

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

    private static RepositorySnapshot Snapshot(IReadOnlyDictionary<string, string> files) =>
        DigestionTestSupport.Snapshot(files.Select(static item =>
            (item.Key, Encoding.UTF8.GetBytes(item.Value))).ToArray());

    private static string AtomPath(DigestionLedgerEntry entry) =>
        $"{BackfillInventoryLoader.RootPath}{entry.SourceId}/residual-open/{entry.AtomId}.yaml";

    private static string Image(RawRepositorySnapshot raw, string? prefix = null) => string.Concat(
        raw.Entries.Where(entry => prefix is null || entry.Path.StartsWith(prefix, StringComparison.Ordinal))
            .OrderBy(static entry => entry.Path, StringComparer.Ordinal)
            .Select(static entry => entry.Path + "\0" + Convert.ToBase64String(entry.Bytes.AsSpan()) + "\n"));

    private static string SourcePrefix(string id) => BackfillInventoryLoader.RootPath + id + "/";

    private static string[] Arguments(params string[] selectors) =>
        ["--base", "baseline", "--report-input-state", "unchanged",
            .. selectors.SelectMany(static selector => new[] { "--source", selector })];

    private static ProductionCliEnvironment Environment(RuleFixture fixture, TemporaryDirectory temporary,
        RawChangeSet? changes = null) => new(temporary.Path,
            new FakeRepositoryGateway(changes ?? RawChangeSet.Create([BetaPath]),
                Raw(fixture.Files), Raw(fixture.Baseline)),
            new FakeLeanReportSource(null), new FakeScribeEmissionVerifier(null));

    private static void WriteFixture(TemporaryDirectory temporary, RuleFixture fixture)
    {
        DirectoryLedgerTestSupport.Write(temporary.Path, fixture.Files);
        foreach (var (path, text) in fixture.Files.Where(static item => DigestionCasStore.IsCanonicalPath(item.Key)))
        {
            var fullPath = Path.Combine(temporary.Path, path);
            Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
            File.WriteAllText(fullPath, text, new UTF8Encoding(false));
        }
    }


    private static DigestionIngestPlan Plan(BackfillInventoryDocument document, RepositorySnapshot snapshot,
        BackfillInventoryDocument baseline, ImmutableHashSet<string>? sourceIds = null,
        RawChangeSet? changes = null, Func<string, TheoryAtomizer>? atomizer = null,
        Func<string, TheoryAtomizerWithContentKinds>? contentAtomizer = null) =>
        DigestionIngestor.Plan(document, snapshot, baseline, sourceIds: sourceIds,
            changes: changes, atomizerResolver: atomizer, contentKindAtomizerResolver: contentAtomizer);

    private static DigestionLedgerAlignment EmptyAlignment(BackfillInventoryDocument document) => new(
        document.RequireDigestionEntries().ToImmutableDictionary(static entry => entry.AtomId,
            static _ => DigestionReceiptAlignment.Seen, StringComparer.Ordinal),
        ImmutableDictionary<string, DigestionAtom>.Empty,
        ImmutableDictionary<string, ImmutableHashSet<string>>.Empty,
        ImmutableDictionary<string, GenreRegistryCheck>.Empty, [], [], [], [], [], [], []);
}
