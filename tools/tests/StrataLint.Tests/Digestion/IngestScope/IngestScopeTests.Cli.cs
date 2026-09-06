using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestScopeTests
{
    [Theory]
    [InlineData("beta")]
    [InlineData(BetaPath)]
    [InlineData("beta", BetaPath, "beta")]
    public void IngestSourceArguments_AcceptsRepeatedIdsAndPaths_RejectsUnknownBeforeWrites(
        params string[] selectors)
    {
        var fixture = Fixture();
        fixture.Files[BetaPath] += Addition;
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = Raw(fixture.Files);
        var console = new BufferedConsole();
        var exit = CliApplication.Run(["ingest", .. Arguments(selectors)], Environment(fixture, temporary), console);

        Assert.True(exit == 0, console.Error);
        var after = Raw(DirectoryLedgerTestSupport.OverlayRepositoryFiles(temporary, fixture.Files));
        Assert.Equal(Image(before, SourcePrefix("alpha")), Image(after, SourcePrefix("alpha")));
        Assert.Equal(2, BackfillInventoryLoader.Load(Decode(after)).RequireDigestionSources()
            .Single(static source => source.SourceId == "beta").Entries.Length);
    }

    [Theory]
    [InlineData("unknown-id")]
    [InlineData("docs/develop/theory/MISSING.md")]
    [InlineData("")]
    [InlineData("BETA")]
    [InlineData("docs/develop/theory/*.md")]
    public void IngestSourceArguments_UnknownSelectorNamesTheInputAndWritesNothing(string selector)
    {
        var fixture = Fixture();
        fixture.Files[BetaPath] += Addition;
        foreach (var selectors in new[] { new[] { selector }, new[] { "beta", selector } })
        {
            using var temporary = new TemporaryDirectory();
            WriteFixture(temporary, fixture);
            var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
            var console = new BufferedConsole();

            var exit = CliApplication.Run(["ingest", .. Arguments(selectors)], Environment(fixture, temporary), console);

            Assert.NotEqual(0, exit);
            Assert.Contains("USAGE:", console.Error, StringComparison.Ordinal);
            Assert.Contains("--source", console.Error, StringComparison.Ordinal);
            Assert.Contains("'" + selector + "'", console.Error, StringComparison.Ordinal);
            Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        }
    }

    [Fact]
    public void IngestSourceArguments_MissingValueUpdatesUsageWithoutWrites()
    {
        var fixture = Fixture();
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var result = Environment(fixture, temporary).Ingest([.. Arguments(), "--source"]);
        Assert.False(result.Success);
        Assert.Contains("[--source X]...", result.Error, StringComparison.Ordinal);
        Assert.Contains("missing value", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    [Fact]
    public void IngestSourceArguments_OmittedSourceMatchesExistingWholeLedgerBytes()
    {
        var fixture = Fixture();
        fixture.Files[BetaPath] += Addition;
        using var unscoped = new TemporaryDirectory();
        using var scoped = new TemporaryDirectory();
        WriteFixture(unscoped, fixture);
        WriteFixture(scoped, fixture);
        var oldVerb = Environment(fixture, unscoped).Ingest(Arguments());
        var allSources = Environment(fixture, scoped).Ingest(Arguments("beta", "alpha", BetaPath));
        Assert.True(oldVerb.Success, oldVerb.Error);
        Assert.True(allSources.Success, allSources.Error);
        Assert.Equal(DirectoryLedgerTestSupport.RepositoryImage(unscoped),
            DirectoryLedgerTestSupport.RepositoryImage(scoped));
    }

    [Fact]
    public void IngestSourceRegistration_RegistersOnlyNamedUnregisteredMarkdown()
    {
        const string named = "docs/develop/theory/NEW_VOLUME.md";
        const string other = "docs/develop/theory/OTHER_VOLUME.md";
        var fixture = Fixture();
        fixture.Files[named] = Addition;
        fixture.Files[other] = "## Claim 4\n\nOther new fact.\n";
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var result = Environment(fixture, temporary).Ingest(Arguments(named, named));
        Assert.True(result.Success, result.Error);
        var after = Raw(DirectoryLedgerTestSupport.OverlayRepositoryFiles(temporary, fixture.Files));
        var sources = BackfillInventoryLoader.Load(Decode(after)).RequireDigestionSources();
        Assert.Equal(["alpha", "beta", "new-volume"], sources.Select(static source => source.SourceId).Order().ToArray());
        Assert.Single(sources.Single(static source => source.SourceId == "new-volume").Entries);
        Assert.DoesNotContain(after.Entries, static entry => entry.Path.StartsWith(
            "Meta/Digestion/backfill/other-volume/", StringComparison.Ordinal));
        Assert.Contains(after.Entries, entry => entry.Path == DigestionCasStore.Capture(Atom(Addition).RawBytes.AsSpan()).RelativePath);
        Assert.DoesNotContain(after.Entries, entry => entry.Path == DigestionCasStore.Capture(Atom(fixture.Files[other]).RawBytes.AsSpan()).RelativePath);
    }

    [Theory]
    [InlineData("docs/develop/theory/ALPHA_.md", "alpha")]
    [InlineData("docs/develop/theory/SAME_NAME.md", "same-name")]
    public void IngestSourceRegistration_DerivedCollisionFailsBeforeAnyWrite(string named, string id)
    {
        var fixture = Fixture();
        fixture.Files[named] = Addition;
        fixture.Files["docs/develop/theory/same-name.md"] = "## Claim 5\n\nDifferent fact.\n";
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var selectors = id == "alpha" ? new[] { "beta", named }
            : new[] { named, "docs/develop/theory/same-name.md" };
        var result = Environment(fixture, temporary).Ingest(Arguments(selectors));
        Assert.False(result.Success);
        Assert.Contains("USAGE:", result.Error, StringComparison.Ordinal);
        Assert.Contains(named, result.Error, StringComparison.Ordinal);
        Assert.Contains(id, result.Error, StringComparison.Ordinal);
        Assert.Contains("collid", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    [Fact]
    public void IngestSourceRegistration_UnnamedSlugCollisionDoesNotRegisterTheOtherPath()
    {
        const string named = "docs/develop/theory/SAME_NAME.md";
        var fixture = Fixture();
        fixture.Files[named] = Addition;
        fixture.Files["docs/develop/theory/same-name.md"] = "## Claim 5\n\nDifferent fact.\n";
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var result = Environment(fixture, temporary).Ingest(Arguments(named));
        Assert.True(result.Success, result.Error);
        Assert.Equal(named, BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionSources()
            .Single(static source => source.SourceId == "same-name").SourcePath);
    }

    [Fact]
    public void IngestScope_UnselectedNonCanonicalEntryKeepsOriginalBytes()
    {
        var document = Ledger();
        var alpha = document.RequireDigestionSources()[0];
        var entry = alpha.Entries[0];
        var hashes = "sha256:" + new string('a', 64);
        entry = entry with
        {
            Coverage = [new("D5/S0/Carrier/Zeta.z", hashes), new("D5/S0/Carrier/Alpha.a", hashes)],
            Receipts = entry.Receipts with
            {
                Scribe = [new("D5/S0/Carrier/Zeta.z", hashes, hashes), new("D5/S0/Carrier/Alpha.a", hashes, hashes)],
            },
        };
        alpha = alpha with { Entries = [entry], AcknowledgedStale = [entry.AtomId] };
        document = document.WithDigestionSources([alpha, document.RequireDigestionSources()[1]]);
        var fixture = Fixture(document);
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[AtomPath(entry)] = "# preserve entry layout\n\n" + files[AtomPath(entry)].Replace("\n", "\r\n", StringComparison.Ordinal);
        }
        fixture.Files[BetaPath] += Addition;
        var current = BackfillInventoryLoader.Load(Snapshot(fixture.Files));
        var plan = Plan(current, Snapshot(fixture.Files), current, BetaOnly);
        Assert.Same(current.RequireDigestionSources()[0], plan.Document.RequireDigestionSources()[0]);
        Assert.Equal(DirectoryLedgerTestSupport.Image(current.WithDigestionSources([current.RequireDigestionSources()[0]])),
            DirectoryLedgerTestSupport.Image(plan.Document.WithDigestionSources([plan.Document.RequireDigestionSources()[0]])));
        var candidate = IngestCommand.ReplaceLedger(Raw(fixture.Files), current, plan.Document, BetaOnly);
        Assert.Equal(Image(Raw(fixture.Files), SourcePrefix("alpha")), Image(candidate, SourcePrefix("alpha")));

        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var result = Environment(fixture, temporary).Ingest(Arguments("beta"));
        Assert.True(result.Success, result.Error);
        var after = Raw(DirectoryLedgerTestSupport.OverlayRepositoryFiles(temporary, fixture.Files));
        Assert.Equal(Image(Raw(fixture.Files), SourcePrefix("alpha")), Image(after, SourcePrefix("alpha")));

        foreach (var args in new[] { Arguments("alpha"), Arguments() })
        {
            using var preserved = new TemporaryDirectory();
            WriteFixture(preserved, fixture);
            var accepted = Environment(fixture, preserved).Ingest(args);
            Assert.True(accepted.Success, accepted.Error);
            var preservedRaw = Raw(DirectoryLedgerTestSupport.OverlayRepositoryFiles(preserved, fixture.Files));
            Assert.Equal(
                Image(Raw(fixture.Files), SourcePrefix("alpha")),
                Image(preservedRaw, SourcePrefix("alpha")));
        }
    }
}
