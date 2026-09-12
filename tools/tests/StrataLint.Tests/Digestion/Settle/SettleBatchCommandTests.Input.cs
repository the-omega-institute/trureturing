using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.NonpropositionalTestSupport;
using static StrataLint.Tests.SettleAtomCommandTests;

namespace StrataLint.Tests;

public sealed partial class SettleBatchCommandTests
{
    [Theory]
    [InlineData("")]
    [InlineData("requests = []\n")]
    [InlineData("[requests]\natom_id = 'x'\n")]
    [InlineData("requests = ['bad']\n")]
    [InlineData("unknown = true\n[[requests]]\natom_id = 'x'\n")]
    [InlineData("[[requests]]\natom_id = [\n")]
    [InlineData("[[requests]]\natom_id = 'x'")]
    [InlineData("[[requests]]\r\natom_id = 'x'\r\n")]
    [InlineData("\uFEFF[[requests]]\natom_id = 'x'\n")]
    public void BatchRejectsInvalidEnvelopeBeforeWrites(string text)
    {
        var fixture = AtomContextFixture.Create();
        using var temporary = new TemporaryDirectory();
        var raw = fixture.RawSnapshot();
        WriteFiles(temporary.Path, raw);
        var before = Image(temporary);
        var result = Batch(temporary, raw, text);
        Assert.False(result.Success);
        Assert.StartsWith("SETTLE_BATCH_INPUT_INVALID", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, Image(temporary));
    }

    [Theory]
    [InlineData("atom_id", "REQUEST_KEYS_INVALID")]
    [InlineData("justification", "REQUEST_KEYS_INVALID")]
    [InlineData("previous_atom_id", "REQUEST_KEYS_INVALID")]
    [InlineData("next_atom_id", "REQUEST_KEYS_INVALID")]
    [InlineData("blank", "REQUEST_VALUE_BLANK")]
    [InlineData("extra", "REQUEST_KEYS_INVALID")]
    [InlineData("neighbor", "ARGUMENTS_INVALID")]
    [InlineData("type", "REQUEST_VALUE_BLANK")]
    public void BatchPreservesRequestSchemaRejections(string change, string code)
    {
        var fixture = AtomContextFixture.Create();
        var id = AtomContextFixture.Id(fixture.Atomized.Claims[1]);
        var request = Request(fixture, id);
        request = change switch
        {
            "blank" => request.Replace(Reason, "   ", StringComparison.Ordinal),
            "extra" => request + "extra = true\n",
            "neighbor" => request.Replace(AtomContextFixture.Id(fixture.Atomized.Claims[0]), "invalid", StringComparison.Ordinal),
            "type" => request.Replace($"'{Reason}'", "true", StringComparison.Ordinal),
            _ => string.Join('\n', request.Split('\n').Where(line => !line.StartsWith(change + " =", StringComparison.Ordinal))),
        };
        Reject(fixture, request, code);
    }

    [Fact]
    public void BatchRejectsDuplicateByReadingPriorWrite()
    {
        var fixture = AtomContextFixture.Create();
        var id = AtomContextFixture.Id(fixture.Atomized.Claims[1]);
        var request = "[[requests]]\n" + Request(fixture, id);
        using var temporary = new TemporaryDirectory();
        var raw = fixture.RawSnapshot();
        WriteFiles(temporary.Path, raw);
        var result = Batch(temporary, raw, request + request);
        Assert.False(result.Success);
        Assert.Contains($"SETTLE_BATCH_STOP record=2 atom_id={id} settled=1 requested=2", result.Error, StringComparison.Ordinal);
        Assert.Contains("SETTLE_INVALID NOT_RESIDUAL_OPEN", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void BatchMatchesSequentialSingleWritesAndPreservesJustification()
    {
        var fixture = AtomContextFixture.Create();
        var requests = fixture.Atomized.Claims.Select(atom => Request(fixture, AtomContextFixture.Id(atom))
            .Replace(Reason, "调用方判断: no proposition; \"quoted\" \\ literal", StringComparison.Ordinal)).ToArray();
        using var single = new TemporaryDirectory();
        using var batch = new TemporaryDirectory();
        WriteFiles(single.Path, fixture.RawSnapshot());
        WriteFiles(batch.Path, fixture.RawSnapshot());
        foreach (var request in requests) Assert.True(Run(single.Path, ReadFiles(single), request).Success);
        var result = Batch(batch, fixture.RawSnapshot(), string.Concat(requests.Select(request => "[[requests]]\n" + request)));
        Assert.True(result.Success, result.Error);
        Assert.EndsWith("SETTLE_BATCH settled=3 requested=3\n", result.Output, StringComparison.Ordinal);
        Assert.Equal(Image(single), Image(batch));
    }

    [Fact]
    public void BatchSelectsSecondOccurrenceWithDistinctNeighbors()
    {
        var fixture = AtomContextFixture.Create(AtomContextFixture.ThreeClaims + "\n## Other\n\nOther.\n\n");
        var id = AtomContextFixture.Id(fixture.Atomized.Claims[1]);
        var previous = AtomContextFixture.Id(fixture.Atomized.Claims[3]);
        fixture = fixture with { SourceBytes = fixture.SourceBytes.Concat(fixture.Atomized.Claims[1].RawBytes).ToArray() };
        var request = $"[[requests]]\natom_id = '{id}'\njustification = '{Reason}'\nprevious_atom_id = '{previous}'\nnext_atom_id = 'source-boundary'\noccurrence_index = 2\n";
        using var temporary = new TemporaryDirectory();
        var raw = fixture.RawSnapshot();
        WriteFiles(temporary.Path, raw);
        var result = Batch(temporary, raw, request);
        Assert.True(result.Success, result.Error);
        var entry = BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries().Single(entry => entry.AtomId == id);
        Assert.Equal(previous, entry.Receipts.Nonpropositional!.PreviousAtomId);
        Assert.Null(entry.Receipts.Nonpropositional.NextAtomId);
    }
}
