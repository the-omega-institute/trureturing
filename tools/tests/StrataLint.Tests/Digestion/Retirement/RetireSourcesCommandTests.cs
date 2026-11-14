using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.SettleAtomCommandTests;

namespace StrataLint.Tests;

public sealed class RetireSourcesCommandTests
{
    private const string Source = "docs/develop/theory/RetirementFixture.md";
    private const string Archive = "docs/develop/archive/theory/RetirementFixture.md";

    [Theory]
    [InlineData("archive")]
    [InlineData("delete")]
    public void PreviewDoesNotWriteAndCommitRemovesOnlyTheSelectedIntakeUnit(string mode)
    {
        using var directory = new TemporaryDirectory();
        var raw = Fixture();
        WriteFiles(directory.Path, raw);
        var report = new FakeLeanReportSource(null);
        var before = Image(directory);
        var gateway = Gateway(directory);
        var preview = RetireSourcesCommand.Run(directory.Path, gateway, report, Args(mode));
        Assert.True(preview.Success, preview.Error);
        Assert.StartsWith("RETIRE_PREVIEW", preview.Output, StringComparison.Ordinal);
        Assert.Equal(before, Image(directory));
        var result = RetireSourcesCommand.Run(directory.Path, gateway, report, Args(mode, write: true));
        Assert.True(result.Success, result.Error);
        Assert.StartsWith("RETIRE_WRITTEN", result.Output, StringComparison.Ordinal);
        var after = ReadFiles(directory);
        Assert.DoesNotContain(after.Entries, entry => entry.Path == Source
            || entry.Path.StartsWith(BackfillInventoryLoader.RootPath + "source/", StringComparison.Ordinal));
        foreach (var original in raw.Entries.Where(entry => entry.Path != Source
                     && !entry.Path.StartsWith(BackfillInventoryLoader.RootPath + "source/", StringComparison.Ordinal)))
            Assert.Equal(original.Bytes, after.Entries.Single(entry => entry.Path == original.Path).Bytes);
        if (mode == "archive")
            Assert.Equal(raw.Entries.Single(entry => entry.Path == Source).Bytes,
                after.Entries.Single(entry => entry.Path == Archive).Bytes);
        else
            Assert.DoesNotContain(after.Entries, entry => entry.Path == Archive);
        Assert.Equal(0, report.CallCount);
        Assert.Equal(0, gateway.WholeTreeReadCount);
        Assert.Empty(gateway.ReadRevisionCalls);
    }

    [Theory]
    [InlineData("open")]
    [InlineData("forged-terminal")]
    [InlineData("cas")]
    [InlineData("new-claim")]
    [InlineData("chain")]
    [InlineData("archive-collision")]
    [InlineData("foreign-chain")]
    [InlineData("foreign-context")]
    [InlineData("incoming-link")]
    public void IncompleteOrReferencedInputRejectsWithoutChangingAnyByte(string defect)
    {
        using var directory = new TemporaryDirectory();
        var raw = Fixture(terminal: defect is not ("open" or "forged-terminal"));
        var atom = raw.Entries.First(entry => entry.Path.EndsWith(".yaml", StringComparison.Ordinal));
        var id = Path.GetFileNameWithoutExtension(atom.Path);
        switch (defect)
        {
            case "forged-terminal":
                raw = Replace(raw, atom.Path, Encoding.UTF8.GetString(atom.Bytes.AsSpan())
                    .Replace("migration: residual", "migration: nonpropositional", StringComparison.Ordinal)
                    .Replace("truth: open", "truth: inapplicable", StringComparison.Ordinal));
                break;
            case "cas": raw = Replace(raw, DigestionCasStore.RootPath + id, "corrupt"); break;
            case "new-claim": raw = Replace(raw, Source, "## New\n\nUnsettled claim.\n"); break;
            case "chain":
                raw = Replace(raw, atom.Path, Encoding.UTF8.GetString(atom.Bytes.AsSpan())
                    .Replace("chain_atoms: []", "chain_atoms:\n    - " + new string('f', 64), StringComparison.Ordinal));
                break;
            case "archive-collision": raw = Add(raw, Archive, "existing archive"); break;
            case "foreign-chain":
                raw = Add(raw, BackfillInventoryLoader.RootPath + "foreign/residual-open/" + new string('f', 64) + ".yaml",
                    "receipts:\n  chain_atoms: [" + id + "]\n");
                break;
            case "foreign-context":
                raw = Add(raw, BackfillInventoryLoader.RootPath + "foreign/context/neighbor.toml", "neighbor = '" + id + "'\n");
                break;
            case "incoming-link": raw = Add(raw, "docs/consumer.md", "[theory](develop/theory/RetirementFixture.md#note)"); break;
        }
        WriteFiles(directory.Path, raw);
        var before = Image(directory);
        var result = RetireSourcesCommand.Run(directory.Path, Gateway(directory), new FakeLeanReportSource(null), Args("archive", true));
        Assert.False(result.Success, defect);
        Assert.Equal(before, Image(directory));
    }

    [Fact]
    public void FailedPublicationRestoresAllOriginalFiles()
    {
        using var directory = new TemporaryDirectory();
        WriteFiles(directory.Path, Fixture());
        var before = Image(directory);
        var result = RetireSourcesCommand.Run(directory.Path, Gateway(directory), new FakeLeanReportSource(null), Args("archive", true),
            commit: (_, _) => throw new IOException("injected archive publication failure"));
        Assert.False(result.Success);
        Assert.Contains("injected", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, Image(directory));
    }

    [Fact]
    public void NewlyCreatedReverseReferenceAbortsBeforeAnyRemoval()
    {
        using var directory = new TemporaryDirectory();
        var raw = Fixture();
        WriteFiles(directory.Path, raw);
        var result = RetireSourcesCommand.Run(directory.Path, Gateway(directory), new FakeLeanReportSource(null), Args("delete", true),
            beforeCommit: () => TemporaryFileSystem.File.WriteAllText(Path.Combine(directory.Path, "docs/consumer.md"), Source));
        Assert.False(result.Success);
        var after = ReadFiles(directory);
        foreach (var original in raw.Entries)
            Assert.Equal(original.Bytes, after.Entries.Single(entry => entry.Path == original.Path).Bytes);
    }

    [Theory]
    [InlineData("../bad")]
    [InlineData("missing")]
    public void InvalidSourceNeverWrites(string selector)
    {
        using var directory = new TemporaryDirectory();
        WriteFiles(directory.Path, Fixture());
        var before = Image(directory);
        var result = RetireSourcesCommand.Run(directory.Path, Gateway(directory), new FakeLeanReportSource(null),
            ["--source", selector, "--mode", "delete", "--write"]);
        Assert.False(result.Success);
        Assert.Equal(before, Image(directory));
    }

    [Fact]
    public void MissingArgumentsCannotTriggerRetirement()
    {
        using var directory = new TemporaryDirectory();
        var result = RetireSourcesCommand.Run(directory.Path, Gateway(directory), new FakeLeanReportSource(null), []);
        Assert.False(result.Success);
        Assert.Contains("USAGE:", result.Error, StringComparison.Ordinal);
    }

    private static string[] Args(string mode, bool write = false) =>
        write ? ["--source", "source", "--mode", mode, "--write"] : ["--source", "source", "--mode", mode];

    private static FakeRepositoryGateway Gateway(TemporaryDirectory directory) =>
        new(RawChangeSet.Create([]), null, null, currentReader: () => ReadFiles(directory));

    private static RawRepositorySnapshot Fixture(bool terminal = true)
    {
        var fixture = AtomContextFixture.Create();
        if (terminal)
        {
            var snapshot = fixture.Snapshot();
            var document = fixture.Ledger;
            fixture = fixture.WithEntries(document.RequireDigestionEntries().Select(entry =>
            {
                var context = Assert.Single(DigestionAtomContextProjection.ResolveOccurrences(snapshot, document, entry.AtomId));
                return entry with
                {
                    ProjectedStatus = new(DigestionMigrationState.Nonpropositional, DigestionTruthState.Inapplicable),
                    Receipts = entry.Receipts with
                    {
                        Nonpropositional = new("Explanatory commentary without a mathematical proposition.", context.Previous?.AtomId, context.Next?.AtomId),
                    },
                };
            }));
        }
        var raw = RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries.Select(entry =>
            RawRepositoryEntry.FromText(entry.Path == AtomContextFixture.SourcePath ? Source : entry.Path,
                Encoding.UTF8.GetString(entry.Bytes.AsSpan()).Replace(AtomContextFixture.SourcePath, Source, StringComparison.Ordinal))));
        raw = DigestionTestSupport.WithSourcePolicy(raw, [Source]);
        var policy = Encoding.UTF8.GetString(raw.Entries.Single(entry => entry.Path == FileMapLoader.RelativePath).Bytes.AsSpan());
        var archivePolicy = "{ pattern = \"docs/develop/archive/theory/**\", kind = \"data\", admission_plane = \"content\", produced_by = \"none\", consumed_by = [\"reader\"], verified_by = [\"SnapshotDecoder\"], artifact_id = \"none\", runtime_disposition = \"committed-source\" }";
        raw = Replace(raw, FileMapLoader.RelativePath, policy.Replace("\n]\n[evidence", ",\n" + archivePolicy + "\n]\n[evidence", StringComparison.Ordinal));
        raw = Add(raw, "D5/Retained.lean", "theorem retained : True := True.intro\n");
        raw = Add(raw, BackfillInventoryLoader.RootPath + "unrelated/source.toml", "intentionally invalid unrelated metadata = [");
        return raw;
    }

    private static RawRepositorySnapshot Add(RawRepositorySnapshot raw, string path, string text) =>
        RawRepositorySnapshot.Create(raw.Entries.Add(RawRepositoryEntry.FromText(path, text)));

    private static RawRepositorySnapshot Replace(RawRepositorySnapshot raw, string path, string text) =>
        RawRepositorySnapshot.Create(raw.Entries.Select(entry => entry.Path == path ? RawRepositoryEntry.FromText(path, text) : entry));
}
