using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.NonpropositionalTestSupport;
using static StrataLint.Tests.SettleAtomCommandTests;

namespace StrataLint.Tests;

public sealed partial class SettleBatchCommandTests
{
    [Theory]
    [InlineData("NOT_RESIDUAL_OPEN")]
    [InlineData("COVERAGE_PRESENT")]
    [InlineData("QUARANTINE_PRESENT")]
    [InlineData("COVER_DISPOSITION_PRESENT")]
    [InlineData("UNRESOLVED_SUBITEMS_PRESENT")]
    [InlineData("CHAIN_PARENT")]
    [InlineData("ATOMIZER_NONE")]
    [InlineData("SOURCE_MISSING")]
    [InlineData("OCCURRENCE_MISSING")]
    [InlineData("ATOM_ABSENT")]
    [InlineData("ATOM_AMBIGUOUS")]
    [InlineData("RECEIPT_PRESENT")]
    public void BatchPreservesSingleRejectionsWithoutWrites(string code)
    {
        var fixture = AtomContextFixture.Create();
        var id = AtomContextFixture.Id(fixture.Atomized.Claims[1]);
        var request = Request(fixture, id);
        var target = fixture.Ledger.RequireDigestionEntries().Single(entry => entry.AtomId == id);
        var updated = code switch
        {
            "NOT_RESIDUAL_OPEN" => target with { ProjectedStatus = new(DigestionMigrationState.Partial, DigestionTruthState.Open) },
            "COVERAGE_PRESENT" => target with { Coverage = [new("D5/S0/Carrier/Probe", null)] },
            "QUARANTINE_PRESENT" => target with { Receipts = target.Receipts with { Quarantine = new("blocked", "supply witness", "missing-prerequisite") } },
            "COVER_DISPOSITION_PRESENT" => target with { Receipts = target.Receipts with { CoverDisposition = new(new(DigestionMigrationState.Partial, DigestionTruthState.Closed), ["D5/S0/Carrier/Probe"], []) } },
            "UNRESOLVED_SUBITEMS_PRESENT" => target with { Receipts = target.Receipts with { UnresolvedSubitems = ["live obligation"] } },
            "CHAIN_PARENT" => target with { Receipts = target.Receipts with { ChainAtoms = [new string('f', 64)] } },
            "ATOMIZER_NONE" => target with { Atomizer = AtomizerRegistry.NoAtomizerId },
            "RECEIPT_PRESENT" => Settled(target) with { ProjectedStatus = target.ProjectedStatus },
            _ => target,
        };
        fixture = fixture.WithEntries(fixture.Ledger.RequireDigestionEntries().Select(entry => entry == target ? updated : entry));
        if (code == "ATOMIZER_NONE") fixture = fixture with { Ledger = fixture.Ledger.WithDigestionSources([
            fixture.Ledger.RequireDigestionSources().Single() with { Atomizer = AtomizerRegistry.NoAtomizerId }]) };
        if (code == "ATOM_AMBIGUOUS")
        {
            var source = fixture.Ledger.RequireDigestionSources().Single();
            fixture = fixture with { Ledger = fixture.Ledger.WithDigestionSources([source,
                source with { SourceId = "second", Entries = [target with { SourceId = "second" }] }]) };
        }
        if (code == "OCCURRENCE_MISSING") fixture = fixture with { SourceBytes = Encoding.UTF8.GetBytes("Other text.\n") };
        if (code == "ATOM_ABSENT") request = request.Replace(id, new string('f', 64), StringComparison.Ordinal);
        using var temporary = new TemporaryDirectory();
        var raw = fixture.RawSnapshot(code != "SOURCE_MISSING");
        WriteFiles(temporary.Path, raw);
        var before = Image(temporary);
        var result = Batch(temporary, raw, "[[requests]]\n" + request);
        Assert.False(result.Success);
        Assert.Contains("SETTLE_INVALID " + (code == "RECEIPT_PRESENT" ? "NOT_RESIDUAL_OPEN" : code), result.Error, StringComparison.Ordinal);
        Assert.Equal(before, Image(temporary));
    }

    [Theory]
    [InlineData("previous")]
    [InlineData("next")]
    [InlineData("previous-boundary")]
    [InlineData("next-boundary")]
    public void BatchRejectsRecomputedAdjacencyMismatch(string side)
    {
        var fixture = AtomContextFixture.Create();
        var id = AtomContextFixture.Id(fixture.Atomized.Claims[1]);
        var request = Request(fixture, id);
        var neighbor = AtomContextFixture.Id(fixture.Atomized.Claims[side.StartsWith("previous", StringComparison.Ordinal) ? 0 : 2]);
        request = request.Replace(neighbor, side.EndsWith("boundary", StringComparison.Ordinal) ? "source-boundary" : new string('f', 64), StringComparison.Ordinal);
        Reject(fixture, request, "CONTEXT_MISMATCH");
    }

    [Fact]
    public void BatchRejectsRepeatedOccurrenceWithoutIndex()
    {
        var fixture = AtomContextFixture.Create();
        var request = Request(fixture, AtomContextFixture.Id(fixture.Atomized.Claims[1]));
        fixture = fixture with { SourceBytes = fixture.SourceBytes.Concat(fixture.SourceBytes).ToArray() };
        Reject(fixture, request, "OCCURRENCE_INDEX_REQUIRED");
    }

    [Theory]
    [InlineData("0", true, "OCCURRENCE_INDEX_INVALID")]
    [InlineData("-1", true, "OCCURRENCE_INDEX_INVALID")]
    [InlineData("99", true, "OCCURRENCE_INDEX_INVALID")]
    [InlineData("2147483648", true, "OCCURRENCE_INDEX_INVALID")]
    [InlineData("'2'", true, "OCCURRENCE_INDEX_INVALID")]
    [InlineData("2", false, "REQUEST_KEYS_INVALID")]
    public void BatchRejectsInvalidOccurrenceIndex(string index, bool repeated, string code)
    {
        var fixture = AtomContextFixture.Create();
        var request = Request(fixture, AtomContextFixture.Id(fixture.Atomized.Claims[1])) + $"occurrence_index = {index}\n";
        if (repeated) fixture = fixture with { SourceBytes = fixture.SourceBytes.Concat(fixture.SourceBytes).ToArray() };
        Reject(fixture, request, code);
    }

    [Fact]
    public void BatchStopsAtFirstFailureAndPreservesOnlyPrefix()
    {
        var fixture = AtomContextFixture.Create();
        var ids = fixture.Atomized.Claims.Select(AtomContextFixture.Id).ToArray();
        var requests = ids.Select(id => "[[requests]]\n" + Request(fixture, id)).ToArray();
        requests[1] += "extra = 'invalid'\n";
        using var temporary = new TemporaryDirectory();
        var raw = fixture.RawSnapshot();
        WriteFiles(temporary.Path, raw);
        var result = Batch(temporary, raw, string.Concat(requests));
        var entries = BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries().ToDictionary(entry => entry.AtomId);
        Assert.Equal(State, StateName(entries[ids[0]].ProjectedStatus));
        Assert.Equal("residual-open", StateName(entries[ids[1]].ProjectedStatus));
        Assert.Equal("residual-open", StateName(entries[ids[2]].ProjectedStatus));
        Assert.False(result.Success);
        Assert.Contains($"SETTLE_BATCH_STOP record=2 atom_id={ids[1]} settled=1 requested=3", result.Error, StringComparison.Ordinal);
        Assert.Contains("SETTLE_INVALID REQUEST_KEYS_INVALID", result.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("SETTLE_BATCH settled=", result.Output, StringComparison.Ordinal);
    }

    private static void Reject(AtomContextFixture fixture, string request, string code)
    {
        using var temporary = new TemporaryDirectory();
        var raw = fixture.RawSnapshot();
        WriteFiles(temporary.Path, raw);
        var before = Image(temporary);
        var result = Batch(temporary, raw, "[[requests]]\n" + request);
        Assert.False(result.Success);
        Assert.Contains("SETTLE_INVALID " + code, result.Error, StringComparison.Ordinal);
        Assert.Equal(before, Image(temporary));
    }

    private static CommandResult Batch(TemporaryDirectory temporary, RawRepositorySnapshot raw, string text)
    {
        using var requestFile = new TemporaryDirectory();
        var path = Path.Combine(requestFile.Path, "requests.toml");
        TemporaryFileSystem.File.WriteAllText(path, text, new UTF8Encoding(false));
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, raw,
            currentReader: () => ReadFiles(temporary));
        var environment = new ProductionCliEnvironment(temporary.Path, gateway, new FakeLeanReportSource(null));
        var console = new BufferedConsole();
        var exit = CliApplication.Run(["settle-batch", "--requests", path, "--base", "baseline"], environment, console);
        return new(exit == 0, console.Output, console.Error, exit);
    }
}
