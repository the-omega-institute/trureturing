using StrataLint.Engine;
using static StrataLint.Tests.UpstreamTestSupport;

namespace StrataLint.Tests;

public sealed partial class BackfillInventoryLoaderTests
{
    [Theory]
    [InlineData("declarations-empty")]
    [InlineData("declarations-default")]
    [InlineData("declaration-newline")]
    [InlineData("rev-upper")]
    [InlineData("rev-short")]
    [InlineData("rev-long")]
    [InlineData("sha-upper")]
    [InlineData("sha-short")]
    [InlineData("sha-prefix")]
    [InlineData("axioms-default")]
    public void UpstreamValueShapeRejectsMalformedReceipt(string mutation)
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var receipt = Settled(fixture.Ledger.RequireDigestionEntries().Single()).Receipts.Upstream!;
        var invalid = mutation switch
        {
            "declarations-empty" => receipt with { Declarations = [] },
            "declarations-default" => receipt with { Declarations = default },
            "declaration-newline" => receipt with { Declarations = ["Nat.add_comm\n"] },
            "rev-upper" => receipt with { MathlibRev = new string('A', 40) },
            "rev-short" => receipt with { MathlibRev = new string('a', 39) },
            "rev-long" => receipt with { MathlibRev = new string('a', 41) },
            "sha-upper" => receipt with { ProbeSha256 = "sha256:" + new string('A', 64) },
            "sha-short" => receipt with { ProbeSha256 = "sha256:" + new string('a', 63) },
            "sha-prefix" => receipt with { ProbeSha256 = new string('a', 64) },
            _ => receipt with { ProbeAxioms = default },
        };
        Assert.False(invalid.IsValid);
    }

    [Fact]
    public void UpstreamReceiptAcceptsSortedAxiomWhitelistAndUnicodeNames()
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = fixture.Ledger.RequireDigestionEntries().Single();
        var loaded = Settled(entry, Receipt().Replace("Nat.add_comm", "Nat.α₁'", StringComparison.Ordinal)
            .Replace("probe_axioms: []", "probe_axioms:\n      - Classical.choice\n      - Quot.sound\n      - propext", StringComparison.Ordinal));
        Assert.True(loaded.Receipts.Upstream!.IsValid);
        Assert.Equal(new[] { "Classical.choice", "Quot.sound", "propext" }, loaded.Receipts.Upstream.ProbeAxioms);
    }
    [Theory]
    [InlineData(" padded reason ")]
    [InlineData("First clause.\nSecond clause.")]
    public void UpstreamJustificationRoundTripsNonblankScalars(string reason)
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = Settled(fixture.Ledger.RequireDigestionEntries().Single());
        entry = entry with { Receipts = entry.Receipts with { Upstream = entry.Receipts.Upstream! with { Justification = reason } } };
        Assert.True(entry.Receipts.Upstream!.IsValid);
        var text = System.Text.Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(entry).AsSpan());
        var raw = RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries.Where(item => item.Path != PathFor(entry, "residual-open"))
            .Append(RawRepositoryEntry.FromText(PathFor(entry), text)));
        var loaded = Assert.Single(BackfillInventoryLoader.Load(Decode(raw)).RequireDigestionEntries());
        Assert.Equal(reason, loaded.Receipts.Upstream!.Justification);
        Assert.Equal(text, System.Text.Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(loaded).AsSpan()));
    }

}
