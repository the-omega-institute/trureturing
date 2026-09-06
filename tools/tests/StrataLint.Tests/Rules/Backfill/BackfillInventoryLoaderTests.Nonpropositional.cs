using System.Text;
using StrataLint.Engine;
using Trureturing.Truth;
using static StrataLint.Tests.NonpropositionalTestSupport;

namespace StrataLint.Tests;

public sealed partial class BackfillInventoryLoaderTests
{
    [Theory]
    [InlineData("coverage")]
    [InlineData("quarantine")]
    [InlineData("cover_disposition")]
    [InlineData("unresolved_subitems")]
    public void NonpropositionalReceiptConflictsAreSl016Red(string conflict)
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = fixture.Ledger.RequireDigestionEntries().Single();
        var receipt = Receipt();
        var text = Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(entry).AsSpan()) + receipt;
        text = conflict switch
        {
            "coverage" => text.Replace("coverage_gids: []", "coverage_gids:\n  - gid: D5/S0/Carrier/Probe\n    target_statement_id: null", StringComparison.Ordinal),
            "quarantine" => text + "  quarantine:\n    justification: blocked\n    reentry_condition: supply witness\n    blocker_class: missing-prerequisite\n",
            "cover_disposition" => text + "  cover_disposition:\n    outcome: partial-closed\n    gids:\n      - D5/S0/Carrier/Probe\n    gaps: []\n",
            "unresolved_subitems" => text.Replace("unresolved_subitems: []", "unresolved_subitems:\n    - live obligation", StringComparison.Ordinal),
            _ => throw new ArgumentOutOfRangeException(nameof(conflict)),
        };
        var error = Assert.Throws<FormatException>(() => LoadNonpropositional(fixture, entry, text));
        Assert.Contains("nonpropositional cannot coexist", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void NonpropositionalReceiptSchemaIsClosedAndRoundTrips()
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = fixture.Ledger.RequireDigestionEntries().Single();
        var original = Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(entry).AsSpan());
        foreach (var receipt in new[] { Receipt(), Receipt(new string('a', 64), new string('b', 64)) })
        {
            var loaded = LoadNonpropositional(fixture, entry, original + receipt);
            Assert.False(loaded.Receipts.IsEmpty);
            Assert.False(loaded.Receipts.IsEmptyForSourceRevision);
            Assert.Equal(original + receipt, Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(loaded).AsSpan()));
            var serialized = Encoding.UTF8.GetString(BackfillInventoryWriter.WriteEntry(loaded).AsSpan());
            var lines = serialized.Split('\n').Skip(3).Where(static line => line.Length > 0).ToArray();
            var yaml = string.Join('\n', lines.Select(static line => line[8..])) + "\n";
            var parsed = BackfillInventoryDocument.ParseEntry(entry.SourceId, entry.SourcePath, entry.Atomizer,
                YamlSubsetParser.Parse(yaml));
            Assert.Equal(serialized, Encoding.UTF8.GetString(BackfillInventoryWriter.WriteEntry(parsed).AsSpan()));
            Assert.Contains("          nonpropositional:\n", serialized, StringComparison.Ordinal);
            Assert.Contains("nonpropositional:", Encoding.UTF8.GetString(BackfillInventoryWriter.WriteStatusAuthorityIdentity(
                fixture.Ledger.RequireDigestionSources().Single(), loaded).AsSpan()), StringComparison.Ordinal);
        }
        foreach (var invalid in new[]
        {
            Receipt() + "    extra: value\n",
            Receipt().Replace("    previous_atom_id: null\n", "", StringComparison.Ordinal),
            Receipt().Replace("    next_atom_id: null\n", "", StringComparison.Ordinal),
            Receipt().Replace($"    justification: {Reason}\n", "", StringComparison.Ordinal),
            Receipt().Replace(Reason, "'   '", StringComparison.Ordinal),
            Receipt().Replace(Reason, "' padded '", StringComparison.Ordinal),
            Receipt("source-boundary"), Receipt("sha256:" + new string('a', 64)),
            Receipt(new string('A', 64)), Receipt(new string('a', 63)), Receipt("'null'"),
            "  nonpropositional: null\n",
        })
            Assert.Throws<FormatException>(() => LoadNonpropositional(fixture, entry, original + invalid));
    }

    [Theory]
    [InlineData("residual-inapplicable")]
    [InlineData("partial-inapplicable")]
    [InlineData("absorbed-inapplicable")]
    [InlineData("nonpropositional-open")]
    [InlineData("nonpropositional-closed")]
    [InlineData("nonpropositional-tail")]
    public void OnlyNonpropositionalInapplicablePairIsLegal(string pair)
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = fixture.Ledger.RequireDigestionEntries().Single();
        var text = Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(entry).AsSpan());
        Assert.True(BackfillInventoryLoader.IsCanonicalPath(PathFor(entry, State)));
        Assert.False(BackfillInventoryLoader.IsCanonicalPath(PathFor(entry, pair)));
        Assert.Contains(pair, Assert.Throws<FormatException>(() => LoadNonpropositional(fixture, entry, text, pair)).Message,
            StringComparison.Ordinal);
        var disposition = text + "  cover_disposition:\n    outcome: " + pair
            + "\n    gids:\n      - D5/S0/Carrier/Probe\n    gaps: []\n";
        Assert.Contains(pair, Assert.Throws<FormatException>(() => LoadNonpropositional(fixture, entry, disposition, "residual-open")).Message,
            StringComparison.Ordinal);
    }

    private static DigestionLedgerEntry LoadNonpropositional(
        AtomContextFixture fixture, DigestionLedgerEntry entry, string yaml, string state = State) =>
        Assert.Single(BackfillInventoryLoader.Load(Decode(RawRepositorySnapshot.Create(
            fixture.RawSnapshot().Entries.Where(item => item.Path != PathFor(entry))
                .Append(RawRepositoryEntry.FromText(PathFor(entry, state), yaml))))).RequireDigestionEntries());
}
