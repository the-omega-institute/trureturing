using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;
using Trureturing.Truth;
using YamlDotNet.Serialization;

namespace StrataLint.Tests;

public sealed class StripScribeReceiptsCommandTests
{
    [Fact]
    public void RootUsageListsStripScribeReceipts()
    {
        var console = new BufferedConsole();
        var environment = new ProductionCliEnvironment(
            "synthetic-repository",
            new FakeRepositoryGateway(RawChangeSet.Create([]), null, null),
            new FakeLeanReportSource(null));

        var exitCode = CliApplication.Run(
            Array.Empty<string>(),
            environment,
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("strip-scribe-receipts", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void PlannerStripsEveryMatchingEntryAcrossAllSources()
    {
        var (fixture, document) = TwoSourceDocumentWithReceipts();
        var result = StripScribeReceiptsCommand.Run(
            "synthetic-repository",
            new FakeRepositoryGateway(RawChangeSet.Create([]), RawWithHistoricalReceipts(fixture, document), RawWithHistoricalReceipts(fixture, document)),
            ["--dry-run"]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(
            $"SCRIBE_STRIP source=alpha-v0.1 atom={document.RequireDigestionSources()[0].Entries[0].AtomId} receipts=2\n"
            + $"SCRIBE_STRIP source=beta-v0.1 atom={document.RequireDigestionSources()[1].Entries[0].AtomId} receipts=1\n"
            + "SCRIBE_STRIP_SUMMARY entries=2 receipts=3 dry_run=true\n",
            result.Output);
    }

    [Fact]
    public void PlannerRejectsUnknownSource()
    {
        var (fixture, document) = TwoSourceDocumentWithReceipts();
        var applyCalls = 0;
        var result = StripScribeReceiptsCommand.Run(
            "synthetic-repository",
            new FakeRepositoryGateway(RawChangeSet.Create([]), RawWithHistoricalReceipts(fixture, document), RawWithHistoricalReceipts(fixture, document)),
            ["--source", "missing-v0.1"],
            (_, _, _) => applyCalls++);

        Assert.False(result.Success);
        Assert.Equal(0, applyCalls);
        Assert.Empty(result.Output);
        Assert.Equal("SCRIBE_STRIP_INVALID unknown source: missing-v0.1\n", result.Error);
    }

    [Fact]
    public void PlannerRejectsValidAndUnknownSourceSelectorsTogether()
    {
        var (fixture, document) = TwoSourceDocumentWithReceipts();
        var applyCalls = 0;
        var result = StripScribeReceiptsCommand.Run(
            "synthetic-repository",
            new FakeRepositoryGateway(RawChangeSet.Create([]), RawWithHistoricalReceipts(fixture, document), RawWithHistoricalReceipts(fixture, document)),
            ["--source", "alpha-v0.1", "--source", "missing-v0.1"],
            (_, _, _) => applyCalls++);

        Assert.False(result.Success);
        Assert.Equal(0, applyCalls);
        Assert.Empty(result.Output);
        Assert.Equal("SCRIBE_STRIP_INVALID unknown source: missing-v0.1\n", result.Error);
    }

    [Fact]
    public void PlannerRejectsDuplicateSourceSelector()
    {
        var (fixture, document) = TwoSourceDocumentWithReceipts();
        var applyCalls = 0;
        var result = StripScribeReceiptsCommand.Run(
            "synthetic-repository",
            new FakeRepositoryGateway(RawChangeSet.Create([]), RawWithHistoricalReceipts(fixture, document), RawWithHistoricalReceipts(fixture, document)),
            ["--source", "alpha-v0.1", "--source", "alpha-v0.1"],
            (_, _, _) => applyCalls++);

        Assert.False(result.Success);
        Assert.Equal(0, applyCalls);
        Assert.Empty(result.Output);
        Assert.Equal("SCRIBE_STRIP_INVALID duplicate source: alpha-v0.1\n", result.Error);
    }

    [Fact]
    public void PlannerStripsOnlySelectedSources()
    {
        var (_, document) = TwoSourceDocumentWithReceipts();
        var originalSources = document.RequireDigestionSources();

        var plan = StripScribeReceiptsCommand.Plan(document, ["beta-v0.1"]);

        var plannedSources = plan.Document.RequireDigestionSources();
        Assert.Equal(originalSources[0].Entries[0], plannedSources[0].Entries[0]);
        Assert.Empty(plannedSources[1].Entries[0].Receipts.Scribe);
        Assert.Equal(
            originalSources[1].Entries[0] with
            {
                Receipts = originalSources[1].Entries[0].Receipts with { Scribe = [] },
            },
            plannedSources[1].Entries[0]);
        var change = Assert.Single(plan.Changes);
        Assert.Equal(("beta-v0.1", originalSources[1].Entries[0].AtomId, 1),
            (change.SourceId, change.AtomId, change.ReceiptCount));
    }

    [Fact]
    public void PlannerRejectsUnparsableEntry()
    {
        var (fixture, document) = TwoSourceDocumentWithReceipts();
        var entry = document.RequireDigestionSources()[0].Entries[0];
        var valid = RawWithHistoricalReceipts(fixture, document);
        var malformed = RawRepositorySnapshot.Create(valid.Entries.Select(rawEntry =>
            rawEntry.Path == CoverageWithoutScribeFixture.EntryPath(entry)
                ? RawRepositoryEntry.FromText(rawEntry.Path, "schema: [unclosed\n")
                : rawEntry));
        var applyCalls = 0;

        var result = StripScribeReceiptsCommand.Run(
            "synthetic-repository",
            new FakeRepositoryGateway(RawChangeSet.Create([]), malformed, RawWithHistoricalReceipts(fixture, document)),
            [],
            (_, _, _) => applyCalls++);

        Assert.False(result.Success);
        Assert.Equal(0, applyCalls);
        Assert.Empty(result.Output);
        Assert.StartsWith("SCRIBE_STRIP_INVALID ", result.Error, StringComparison.Ordinal);
        Assert.EndsWith("\n", result.Error, StringComparison.Ordinal);
        Assert.Equal(1, result.Error.Count(static character => character == '\n'));
        Assert.DoesNotContain('\r', result.Error);
    }

    [Fact]
    public void UnparsableUnselectedEntryAfterValidEntryAbortsWithoutWriting()
    {
        var (fixture, document) = TwoSourceDocumentWithReceipts();
        var entries = document.RequireDigestionEntries();
        var valid = RawWithHistoricalReceipts(fixture, document);
        var malformedPath = CoverageWithoutScribeFixture.EntryPath(entries[1]);
        var malformed = RawRepositorySnapshot.Create(valid.Entries.Select(rawEntry =>
            rawEntry.Path == malformedPath
                ? RawRepositoryEntry.FromText(rawEntry.Path, "schema: [unclosed\n")
                : rawEntry));
        var applyCalls = 0;

        var result = StripScribeReceiptsCommand.Run(
            "synthetic-repository",
            new FakeRepositoryGateway(RawChangeSet.Create([]), malformed, RawWithHistoricalReceipts(fixture, document)),
            ["--source", "alpha-v0.1"],
            (_, _, _) => applyCalls++);

        Assert.False(result.Success);
        Assert.Equal(0, applyCalls);
        Assert.Empty(result.Output);
        Assert.StartsWith("SCRIBE_STRIP_INVALID ", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void EmptyDirectoryLedgerIsRejectedWithoutWriting()
    {
        var (fixture, document) = TwoSourceDocumentWithReceipts();
        var empty = document.WithDigestionSources(document.RequireDigestionSources()
            .Select(static source => source with { Entries = [] })
            .ToImmutableArray());
        var raw = RawWithHistoricalReceipts(fixture, empty);
        var applyCalls = 0;

        var result = StripScribeReceiptsCommand.Run(
            "synthetic-repository",
            new FakeRepositoryGateway(RawChangeSet.Create([]), raw, raw),
            [],
            (_, _, _) => applyCalls++);

        Assert.False(result.Success);
        Assert.Equal(0, applyCalls);
        Assert.Empty(result.Output);
        Assert.Equal("SCRIBE_STRIP_INVALID digestion ledger contains no atom entries\n", result.Error);
    }

    [Fact]
    public void BaseOptionIsRejectedAndNoRevisionIsRead()
    {
        var (fixture, document) = TwoSourceDocumentWithReceipts();
        var repository = new FakeRepositoryGateway(
            RawChangeSet.Create([]),
            RawWithHistoricalReceipts(fixture, document),
            RawWithHistoricalReceipts(fixture, document));
        var applyCalls = 0;

        var result = StripScribeReceiptsCommand.Run(
            "synthetic-repository",
            repository,
            ["--base", "baseline"],
            (_, _, _) => applyCalls++);

        Assert.False(result.Success);
        Assert.Equal(0, applyCalls);
        Assert.Empty(repository.ReadRevisionCalls);
        Assert.Equal(
            "SCRIBE_STRIP_INVALID USAGE: StrataLint strip-scribe-receipts "
            + "[--source SOURCE_ID]... [--dry-run]\n",
            result.Error);
    }

    [Fact]
    public void CliVerbUsesCanonicalWriterAndPreservesUntouchedEntryBytes()
    {
        var (fixture, document) = TwoSourceDocumentWithReceipts();
        var sources = document.RequireDigestionSources();
        var alpha = sources[0].Entries[0];
        var beta = sources[1].Entries[0];
        var files = FilesWithHistoricalReceipts(fixture, document);
        var alphaPath = CoverageWithoutScribeFixture.EntryPath(alpha);
        var betaPath = CoverageWithoutScribeFixture.EntryPath(beta);
        files[betaPath] += "# untouched byte sentinel\n";
        var current = RawRepositorySnapshot.Create(files.Select(static pair =>
            RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, files);
        var betaFullPath = Path.Combine(temporary.Path, betaPath.Replace('/', Path.DirectorySeparatorChar));
        var betaBytes = File.ReadAllBytes(betaFullPath);
        var console = new BufferedConsole();
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create([]), current, current),
            new FakeLeanReportSource(fixture.Inputs.Report));

        var exitCode = CliApplication.Run(
            ["strip-scribe-receipts", "--source", "alpha-v0.1"],
            environment,
            console);

        Assert.Equal(0, exitCode);
        Assert.Empty(console.Error);
        Assert.Equal(
            $"SCRIBE_STRIP source=alpha-v0.1 atom={alpha.AtomId} receipts=2\n"
            + "SCRIBE_STRIP_SUMMARY entries=1 receipts=2 dry_run=false\n",
            console.Output);
        Assert.Equal(betaBytes, File.ReadAllBytes(betaFullPath));
        var written = BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionSources();
        Assert.Empty(written.Single(static source => source.SourceId == "alpha-v0.1")
            .Entries[0].Receipts.Scribe);
        Assert.Single(written.Single(static source => source.SourceId == "beta-v0.1")
            .Entries[0].Receipts.Scribe);
        var expectedAlpha = alpha with { Receipts = alpha.Receipts with { Scribe = [] } };
        Assert.Equal(
            BackfillInventoryWriter.WriteAtom(expectedAlpha).ToArray(),
            File.ReadAllBytes(Path.Combine(
                temporary.Path,
                alphaPath.Replace('/', Path.DirectorySeparatorChar))));
    }

    [Fact]
    public void RealWriterIsIdempotentAcrossReloadedOnDiskOutput()
    {
        var (fixture, document) = TwoSourceDocumentWithReceipts();
        var files = FilesWithHistoricalReceipts(fixture, document);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, files);

        var firstConsole = new BufferedConsole();
        var firstEnvironment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([]),
                DirectoryLedgerTestSupport.ReadRepository(temporary),
                null),
            new FakeLeanReportSource(fixture.Inputs.Report));

        var firstExitCode = CliApplication.Run(
            ["strip-scribe-receipts"],
            firstEnvironment,
            firstConsole);

        Assert.Equal(0, firstExitCode);
        Assert.Empty(firstConsole.Error);
        Assert.EndsWith(
            "SCRIBE_STRIP_SUMMARY entries=2 receipts=3 dry_run=false\n",
            firstConsole.Output,
            StringComparison.Ordinal);
        Assert.All(
            BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries(),
            static entry => Assert.Empty(entry.Receipts.Scribe));
        var afterFirst = DirectoryLedgerTestSupport.RepositoryImage(temporary);

        var secondConsole = new BufferedConsole();
        var secondEnvironment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([]),
                DirectoryLedgerTestSupport.ReadRepository(temporary),
                null),
            new FakeLeanReportSource(fixture.Inputs.Report));

        var secondExitCode = CliApplication.Run(
            ["strip-scribe-receipts"],
            secondEnvironment,
            secondConsole);

        Assert.Equal(0, secondExitCode);
        Assert.Empty(secondConsole.Error);
        Assert.Equal(
            "SCRIBE_STRIP_SUMMARY entries=0 receipts=0 dry_run=false\n",
            secondConsole.Output);
        Assert.Equal(afterFirst, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    [Fact]
    public void DryRunReportsEveryPlannedEntryWithoutWriting()
    {
        var (fixture, document) = TwoSourceDocumentWithReceipts();
        var applyCalls = 0;
        var result = StripScribeReceiptsCommand.Run(
            "synthetic-repository",
            new FakeRepositoryGateway(RawChangeSet.Create([]), RawWithHistoricalReceipts(fixture, document), RawWithHistoricalReceipts(fixture, document)),
            ["--dry-run"],
            (_, _, _) => applyCalls++);

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, applyCalls);
        Assert.Equal(2, result.Output.Split('\n').Count(static line =>
            line.StartsWith("SCRIBE_STRIP source=", StringComparison.Ordinal)));
        Assert.EndsWith(
            "SCRIBE_STRIP_SUMMARY entries=2 receipts=3 dry_run=true\n",
            result.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void ReportOrderIsCanonicalAcrossSnapshotEnumerationOrder()
    {
        var (fixture, document) = TwoSourceDocumentWithReceipts();
        var forward = RawWithHistoricalReceipts(fixture, document);
        var reverse = RawRepositorySnapshot.Create(forward.Entries.Reverse());

        var first = StripScribeReceiptsCommand.Run(
            "synthetic-repository",
            new FakeRepositoryGateway(RawChangeSet.Create([]), forward, null),
            ["--dry-run"]);
        var second = StripScribeReceiptsCommand.Run(
            "synthetic-repository",
            new FakeRepositoryGateway(RawChangeSet.Create([]), reverse, null),
            ["--dry-run"]);

        Assert.True(first.Success, first.Error);
        Assert.True(second.Success, second.Error);
        Assert.Equal(first.Output, second.Output);
        Assert.Equal(
            $"SCRIBE_STRIP source=alpha-v0.1 atom={document.RequireDigestionSources()[0].Entries[0].AtomId} receipts=2\n"
            + $"SCRIBE_STRIP source=beta-v0.1 atom={document.RequireDigestionSources()[1].Entries[0].AtomId} receipts=1\n"
            + "SCRIBE_STRIP_SUMMARY entries=2 receipts=3 dry_run=true\n",
            second.Output);
    }

    [Fact]
    public void CliVerbSucceedsWhenNoReceiptsNeedStripping()
    {
        var (fixture, withReceipts) = TwoSourceDocumentWithReceipts();
        var document = withReceipts.WithDigestionSources(withReceipts.RequireDigestionSources()
            .Select(source => source with
            {
                Entries = source.Entries.Select(entry => entry with
                {
                    Receipts = entry.Receipts with { Scribe = [] },
                }).ToImmutableArray(),
            }).ToImmutableArray());
        var result = StripScribeReceiptsCommand.Run(
            "synthetic-repository",
            new FakeRepositoryGateway(RawChangeSet.Create([]), RawWithHistoricalReceipts(fixture, document), RawWithHistoricalReceipts(fixture, document)),
            [],
            static (_, _, _) => { });

        Assert.True(result.Success, result.Error);
        Assert.Equal("SCRIBE_STRIP_SUMMARY entries=0 receipts=0 dry_run=false\n", result.Output);
    }

    [Fact]
    public void ValidationFailureReasonIsOneLine()
    {
        var result = StripScribeReceiptsCommand.Run(
            "synthetic-repository",
            new MultilineFailureRepositoryGateway(),
            [],
            static (_, _, _) => { });

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Equal("SCRIBE_STRIP_INVALID first line second line\n", result.Error);
    }

    private static (CoverageWithoutScribeFixture Fixture, BackfillInventoryDocument Document)
        TwoSourceDocumentWithReceipts()
    {
        var fixture = new CoverageWithoutScribeFixture(2);
        var template = Assert.Single(fixture.Document.RequireDigestionSources());
        var entries = template.Entries.Select((entry, index) => entry with
        {
            SourceId = index == 0 ? "alpha-v0.1" : "beta-v0.1",
            SourcePath = index == 0 ? "theory/alpha.md" : "theory/beta.md",
            Receipts = entry.Receipts with
            {
                Scribe = Enumerable.Repeat(
                    new DigestionScribeReceipt(
                        entry.Coverage[0].Gid,
                        "sha256:" + new string('a', 64),
                        "sha256:" + new string('b', 64)),
                    index == 0 ? 2 : 1).ToImmutableArray(),
            },
        }).ToArray();
        var document = fixture.Document.WithDigestionSources([
            template with
            {
                SourceId = entries[0].SourceId,
                SourcePath = entries[0].SourcePath,
                Entries = [entries[0]],
            },
            template with
            {
                SourceId = entries[1].SourceId,
                SourcePath = entries[1].SourcePath,
                Entries = [entries[1]],
            },
        ]);
        return (fixture, document);
    }

    private static RawRepositorySnapshot RawWithHistoricalReceipts(
        CoverageWithoutScribeFixture fixture,
        BackfillInventoryDocument document) =>
        RawRepositorySnapshot.Create(FilesWithHistoricalReceipts(fixture, document)
            .Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));

    private static Dictionary<string, string> FilesWithHistoricalReceipts(
        CoverageWithoutScribeFixture fixture,
        BackfillInventoryDocument document)
    {
        var files = new Dictionary<string, string>(fixture.Files, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(files, document);
        // The current writer omits Scribe receipts; legacy input belongs to the fixture.
        foreach (var entry in document.RequireDigestionEntries())
        {
            if (entry.Receipts.Scribe.IsEmpty)
            {
                continue;
            }

            var path = CoverageWithoutScribeFixture.EntryPath(entry);
            var root = Assert.IsType<Dictionary<string, object?>>(YamlSubsetParser.Parse(files[path]));
            var receipts = Assert.IsType<Dictionary<string, object?>>(root["receipts"]);
            receipts.Add("scribe", entry.Receipts.Scribe.Select(receipt =>
                new Dictionary<string, object?>
                {
                    { "gid", receipt.Gid },
                    { "definition_sha256", receipt.DefinitionSha256 },
                    { "emission_sha256", receipt.EmissionSha256 },
                }).ToArray());
            files[path] = new SerializerBuilder().WithIndentedSequences().Build().Serialize(root);
        }

        return files;
    }

    private sealed class MultilineFailureRepositoryGateway : IRepositoryGateway
    {
        public AdmissionTopologyOutcome InspectAdmissionTopology() => throw Unsupported();
        public PreparedRepository Prepare(string? protectedBase) => throw Unsupported();
        public FrozenRevisionIdentity ResolveCurrentRevision() => throw Unsupported();
        public RawRepositorySnapshot ReadCurrent() =>
            throw new InvalidOperationException("first line\nsecond line");
        public RawRepositorySnapshot ReadRevision(string revision) => throw Unsupported();
        public RawChangeSet ReadCurrentChanges() => throw Unsupported();
        public RawChangeSet ReadChanges(string revision) => throw Unsupported();

        private static NotSupportedException Unsupported() => new();
    }
}
