using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestScopeTests
{
    private const string ClauseText = "## Claim 10\n\n- First clause.\n- Second clause.\n";

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

    private static BackfillInventoryDocument TwoSourceLedger(
        DigestionLedgerSource alpha,
        DigestionLedgerSource beta) =>
        BackfillInventoryDocument.Create([alpha, beta], []);

    private static DigestionLedgerSource EmptySource(string id, string path) =>
        new(
            id,
            path,
            AtomizerRegistry.GenericId,
            [],
            GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry),
            []);

    private static IReadOnlyDictionary<string, ImmutableArray<byte>> ExistingLedgerFiles(
        IReadOnlyDictionary<string, string> files) =>
        files
            .Where(static item => BackfillInventoryLoader.IsCanonicalPath(item.Key))
            .ToDictionary(
                static item => item.Key,
                static item => ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(item.Value)),
                StringComparer.Ordinal);

    private static void AssertExistingLedgerFilesUnchanged(
        IReadOnlyDictionary<string, ImmutableArray<byte>> before,
        RawRepositorySnapshot after)
    {
        var afterByPath = after.Entries.ToDictionary(static item => item.Path, StringComparer.Ordinal);
        foreach (var (path, bytes) in before)
        {
            Assert.True(afterByPath.TryGetValue(path, out var entry), $"existing path removed: {path}");
            Assert.Equal(bytes.ToArray(), entry.Bytes.ToArray());
        }
    }

    private static string[] PreservedRows(CommandResult result) =>
        result.Output.Split('\n', StringSplitOptions.RemoveEmptyEntries)
            .Where(static line => line.StartsWith(
                "INGEST_PRESERVED_EXISTING ", StringComparison.Ordinal))
            .ToArray();

    private static void AssertObservation(
        CommandResult result,
        string atomId,
        string sourceId,
        string kind)
    {
        Assert.Contains(
            $"INGEST_PRESERVED_EXISTING atom={atomId} source={sourceId} kind={kind}",
            PreservedRows(result));
        AssertSummaryCountMatchesRows(result);
    }

    private static void AssertNoObservation(
        CommandResult result,
        string atomId,
        string sourceId,
        string kind)
    {
        Assert.DoesNotContain(
            $"INGEST_PRESERVED_EXISTING atom={atomId} source={sourceId} kind={kind}",
            PreservedRows(result));
        AssertSummaryCountMatchesRows(result);
    }

    private static void AssertSummaryCountMatchesRows(CommandResult result)
    {
        var rows = PreservedRows(result);
        var summary = Assert.Single(result.Output.Split('\n'), static line =>
            line.StartsWith("INGEST ", StringComparison.Ordinal));
        var field = Assert.Single(summary.Split(' '), static token =>
            token.StartsWith("preserved_existing=", StringComparison.Ordinal));
        Assert.Equal(rows.Length, int.Parse(
            field["preserved_existing=".Length..],
            System.Globalization.CultureInfo.InvariantCulture));
    }

    private static RawRepositorySnapshot Overlay(
        TemporaryDirectory temporary,
        RuleFixture fixture) =>
        Raw(DirectoryLedgerTestSupport.OverlayRepositoryFiles(temporary, fixture.Files));
}
