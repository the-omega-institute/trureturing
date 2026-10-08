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
        var before = DirectoryLedgerTestSupport.ReadRepository(temporary);
        var console = new BufferedConsole();
        var exit = CliApplication.Run(["ingest", .. Arguments(selectors)], Environment(fixture, temporary), console);

        Assert.True(exit == 0, console.Error);
        var after = DirectoryLedgerTestSupport.ReadRepository(temporary);
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
        Assert.Contains("--source X", result.Error, StringComparison.Ordinal);
        Assert.Contains("missing value", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    [Fact]
    public void IngestSourceArguments_OmittedSourceFailsBeforeReading()
    {
        var fixture = Fixture();
        fixture.Files[BetaPath] += Addition;
        using var unscoped = new TemporaryDirectory();
        WriteFixture(unscoped, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(unscoped);
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), Raw(fixture.Files), Raw(fixture.Baseline));
        var result = IngestCommand.RunReportFree(unscoped.Path, gateway, Arguments());
        Assert.False(result.Success);
        Assert.Contains("--source", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, gateway.ReadCurrentCount);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(unscoped));
    }

    [Theory]
    [InlineData("Meta/Digestion/backfill/unrelated/source.toml")]
    [InlineData("Meta/Digestion/backfill/beta/residual-open/aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.yaml")]
    public void IngestIgnoresUnrelatedMalformedRecords(string path)
    {
        var fixture = Fixture();
        fixture.Files[path] = "malformed [";
        fixture.Files[BetaPath] += Addition;
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var result = Environment(fixture, temporary).Ingest(Arguments("beta"));
        Assert.True(result.Success, result.Error);
        var after = DirectoryLedgerTestSupport.ReadRepository(temporary);
        Assert.Contains(after.Entries, entry => entry.Path == path);
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
        var after = DirectoryLedgerTestSupport.ReadRepository(temporary);
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
    public void IngestScope_UnselectedEntryWithNonCanonicalLayoutKeepsOriginalBytes()
    {
        var document = Ledger();
        var alpha = document.RequireDigestionSources()[0];
        var entry = alpha.Entries[0];
        var hashes = "sha256:" + new string('a', 64);
        entry = entry with
        {
            Coverage = [new("D5/S0/Carrier/Zeta.z", hashes), new("D5/S0/Carrier/Alpha.a", hashes)],
        };
        alpha = alpha with { Entries = [entry], AcknowledgedStale = [entry.AtomId] };
        document = document.WithDigestionSources([alpha, document.RequireDigestionSources()[1]]);
        var fixture = Fixture(document);
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            var text = files[AtomPath(entry)];
            // The layout the canonical writer would never produce: a leading comment and CRLF
            // line endings. (This used to inject a historical `receipts.scribe` block; that key
            // is now rejected outright, so the non-canonical marker has to be one that loads.)
            Assert.DoesNotContain("scribe:", text, StringComparison.Ordinal);
            files[AtomPath(entry)] = "# preserve entry layout\r\n\r\n"
                + text.Replace("\n", "\r\n", StringComparison.Ordinal);
        }
        fixture.Files[BetaPath] += Addition;

        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.ReadRepository(temporary);
        var result = Environment(fixture, temporary).Ingest(Arguments("beta"));
        Assert.True(result.Success, result.Error);
        var after = DirectoryLedgerTestSupport.ReadRepository(temporary);
        Assert.Equal(Image(before, SourcePrefix("alpha")), Image(after, SourcePrefix("alpha")));

        foreach (var args in new[] { Arguments("alpha"), Arguments("alpha", "beta") })
        {
            using var preserved = new TemporaryDirectory();
            WriteFixture(preserved, fixture);
            var beforePreserved = DirectoryLedgerTestSupport.ReadRepository(preserved);
            var accepted = Environment(fixture, preserved).Ingest(args);
            Assert.True(accepted.Success, accepted.Error);
            var preservedRaw = DirectoryLedgerTestSupport.ReadRepository(preserved);
            Assert.Equal(
                Image(beforePreserved, SourcePrefix("alpha")),
                Image(preservedRaw, SourcePrefix("alpha")));
        }
    }

    [Theory]
    [InlineData(null)]
    [InlineData("alpha")]
    [InlineData("beta")]
    public void IngestScope_MalformedMatchingCoverageIsLocal(string? sourceId)
    {
        var document = Ledger();
        var alpha = document.RequireDigestionSources()[0];
        var entry = alpha.Entries[0] with
        {
            Coverage = [new("D5/S0/Carrier/Alpha.a", null), new("D5/S0/Carrier/Zeta.z", null)],
        };
        document = document.WithDigestionSources(
            [alpha with { Entries = [entry] }, document.RequireDigestionSources()[1]]);
        var fixture = Fixture(document);
        var path = AtomPath(entry);
        const string first = "  - gid: D5/S0/Carrier/Alpha.a\n    target_statement_id: null\n";
        const string second = "  - gid: D5/S0/Carrier/Zeta.z\n    target_statement_id: null\n";
        Assert.Contains(first + second, fixture.Files[path], StringComparison.Ordinal);
        fixture.Files[path] = fixture.Files[path].Replace(first + second, second + first, StringComparison.Ordinal);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);

        var result = Environment(fixture, temporary).Ingest(
            sourceId is null ? Arguments("alpha", "beta") : Arguments(sourceId));

        if (sourceId == "beta") Assert.True(result.Success, result.Error);
        else
        {
            Assert.False(result.Success);
            Assert.Contains("BACKFILL_COVERAGE_ORDER", result.Error, StringComparison.Ordinal);
        }
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }
}
