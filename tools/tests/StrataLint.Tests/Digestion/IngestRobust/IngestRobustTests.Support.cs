using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestRobustTests
{
    private const string AlphaPath = "docs/develop/theory/ALPHA.md";
    private const string BetaPath = "docs/develop/theory/BETA.md";
    private const string AlphaText = "## Claim 1\n\nAlpha fact.\n\n";
    private const string BetaText = "## Claim 2\n\nBeta fact.\n\n";
    private const string Addition = "## Claim 3\n\nAdditional fact.\n";
    private const string ClauseText = "## Claim 10\n\n- First clause.\n- Second clause.\n";

    private static DigestionAtom Atom(string text) => Assert.Single(
        GenericAtomizer.Atomize(
            Encoding.UTF8.GetBytes(text),
            DigestionTestSupport.Rules).Claims);

    private static DigestionLedgerSource Source(
        string id,
        string path,
        string text,
        bool populated = true)
    {
        var atom = Atom(text);
        return new DigestionLedgerSource(
            id,
            path,
            AtomizerRegistry.GenericId,
            [],
            GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry),
            populated
                ?
                [
                    DigestionTestSupport.Entry(
                        atom,
                        atom.Fingerprints.RawSha256["sha256:".Length..],
                        AtomizerRegistry.GenericId,
                        sourceId: id,
                        sourcePath: path),
                ]
                : []);
    }

    private static DigestionLedgerSource EmptySource(string id, string path) =>
        new(
            id,
            path,
            AtomizerRegistry.GenericId,
            [],
            GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry),
            []);

    private static BackfillInventoryDocument Ledger(bool populated = true) =>
        TwoSourceLedger(
            Source("alpha", AlphaPath, AlphaText, populated),
            Source("beta", BetaPath, BetaText, populated));

    private static BackfillInventoryDocument TwoSourceLedger(
        DigestionLedgerSource alpha,
        DigestionLedgerSource beta) =>
        BackfillInventoryDocument.Create([alpha, beta], []);

    private static RuleFixture Fixture(
        BackfillInventoryDocument? ledger = null,
        string alphaText = AlphaText,
        string betaText = BetaText)
    {
        ledger ??= Ledger();
        return RobustFixture(ledger, ledger, alphaText, betaText);
    }

    private static RuleFixture RobustFixture(
        BackfillInventoryDocument current,
        BackfillInventoryDocument baseline,
        string alphaText = AlphaText,
        string betaText = BetaText)
    {
        var fixture = new RuleFixture();
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files.Remove(RuleFixture.FixtureDigestionSourcePath);
            files.Remove(RuleFixture.FixtureCasPath);
            files[AlphaPath] = alphaText;
            files[BetaPath] = betaText;
        }

        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Files, current);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Baseline, baseline);
        AddEntryCas(fixture.Files, current);
        AddEntryCas(fixture.Baseline, baseline);
        return fixture;
    }

    private static void AddEntryCas(
        IDictionary<string, string> files,
        BackfillInventoryDocument document)
    {
        foreach (var entry in document.RequireDigestionEntries())
        {
            var sourceText = entry.SourceId == "alpha" ? files[AlphaPath] : files[BetaPath];
            var atom = GenericAtomizer.Atomize(
                    Encoding.UTF8.GetBytes(sourceText),
                    DigestionTestSupport.Rules)
                .Claims
                .FirstOrDefault(candidate => candidate.Fingerprints.RawSha256 == entry.CasRef);
            if (atom is not null)
            {
                AddCas(files, atom);
            }
        }
    }

    private static void AddCas(IDictionary<string, string> files, DigestionAtom atom)
    {
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        files[captured.RelativePath] = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
    }

    private static RawRepositorySnapshot Raw(IReadOnlyDictionary<string, string> files) =>
        RawRepositorySnapshot.Create(files.Select(static item =>
            RawRepositoryEntry.FromText(item.Key, item.Value)));

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

    private static string AtomPath(DigestionLedgerEntry entry) =>
        $"{BackfillInventoryLoader.RootPath}{entry.SourceId}/residual-open/{entry.AtomId}.yaml";

    private static string SourcePrefix(string id) =>
        BackfillInventoryLoader.RootPath + id + "/";

    private static string[] Arguments(params string[] selectors) =>
        [
            "--base",
            "baseline",
            .. selectors.SelectMany(static selector => new[] { "--source", selector }),
        ];

    private static ProductionCliEnvironment Environment(
        RuleFixture fixture,
        TemporaryDirectory temporary,
        RawChangeSet? changes = null,
        ReportFreeIngestDependencies? dependencies = null) =>
        new(
            temporary.Path,
            new FakeRepositoryGateway(
                changes ?? RawChangeSet.Create([BetaPath]),
                Raw(fixture.Files),
                Raw(fixture.Baseline)),
            new FakeLeanReportSource(null),
            new FakeScribeEmissionVerifier(null),
            reportFreeIngestDependencies: dependencies);

    private static void WriteFixture(TemporaryDirectory temporary, RuleFixture fixture)
    {
        foreach (var (path, text) in fixture.Files)
        {
            var fullPath = Path.Combine(temporary.Path, path);
            Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
            File.WriteAllText(fullPath, text, new UTF8Encoding(false));
        }
    }

    private static void AssertExistingLedgerFilesUnchanged(
        RawRepositorySnapshot before,
        RawRepositorySnapshot after)
    {
        var afterByPath = after.Entries.ToDictionary(static item => item.Path, StringComparer.Ordinal);
        foreach (var old in before.Entries)
        {
            Assert.True(afterByPath.TryGetValue(old.Path, out var entry), $"existing path removed: {old.Path}");
            Assert.Equal(old.Bytes.ToArray(), entry.Bytes.ToArray());
        }
    }
}
