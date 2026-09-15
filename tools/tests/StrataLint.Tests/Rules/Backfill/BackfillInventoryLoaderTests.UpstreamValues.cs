using System.Text;
using StrataLint.Engine;
using Trureturing.Truth;
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
    public static TheoryData<string, bool> JustificationScalars
    {
        get
        {
            var data = new TheoryData<string, bool>();
            foreach (var reason in new[]
            {
                " padded reason ", "First clause.\nSecond clause.",
                "\"quoted reason\"", "'quoted reason'",
                "First clause: commutativity.\nSecond clause: normalization.",
                "# leading comment", " # padded comment", "inline # comment", "trailing space ",
                "quote: \"x\"; slash: \\; literal: \\n; actual:\r\nnext\tclause",
                "control\0\b\f\u001f\u007fend", "Unicode α₁ → β 😀", "null", "[]", "123", "|-",
            })
            {
                data.Add(reason, false);
                data.Add(reason, true);
            }
            return data;
        }
    }

    [Theory]
    [MemberData(nameof(JustificationScalars))]
    public void UpstreamJustificationRoundTripsNonblankScalars(string reason, bool legacyEntry)
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = Settled(fixture.Ledger.RequireDigestionEntries().Single());
        entry = entry with { Receipts = entry.Receipts with { Upstream = entry.Receipts.Upstream! with { Justification = reason } } };
        Assert.True(entry.Receipts.Upstream!.IsValid);
        var loaded = RoundTripJustification(fixture, entry, legacyEntry);
        Assert.Equal(reason, loaded.Receipts.Upstream!.Justification);
    }

    [Theory]
    [MemberData(nameof(JustificationScalars))]
    public void NonpropositionalJustificationRoundTripsNonblankScalars(string reason, bool legacyEntry)
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = NonpropositionalTestSupport.Settled(fixture.Ledger.RequireDigestionEntries().Single());
        entry = entry with { Receipts = entry.Receipts with
        {
            Nonpropositional = entry.Receipts.Nonpropositional! with { Justification = reason },
        } };
        // Nonpropositional receipts retain their existing trimmed-justification contract.
        if (reason != reason.Trim())
        {
            Assert.False(entry.Receipts.Nonpropositional!.IsValid);
            Assert.Throws<FormatException>(() => RoundTripJustification(fixture, entry, legacyEntry));
            return;
        }
        Assert.True(entry.Receipts.Nonpropositional!.IsValid);
        var loaded = RoundTripJustification(fixture, entry, legacyEntry);
        Assert.Equal(reason, loaded.Receipts.Nonpropositional!.Justification);
    }

    private static DigestionLedgerEntry RoundTripJustification(
        AtomContextFixture fixture, DigestionLedgerEntry entry, bool legacyEntry)
    {
        var text = Encoding.UTF8.GetString((legacyEntry
            ? BackfillInventoryWriter.WriteEntry(entry) : BackfillInventoryWriter.WriteAtom(entry)).AsSpan());
        DigestionLedgerEntry loaded;
        if (legacyEntry)
        {
            var lines = text.Split('\n').Skip(3).Where(static line => line.Length > 0);
            var yaml = string.Join('\n', lines.Select(static line => line[8..])) + "\n";
            loaded = BackfillInventoryDocument.ParseEntry(entry.SourceId, entry.SourcePath, entry.Atomizer,
                YamlSubsetParser.Parse(yaml));
        }
        else
        {
            var raw = RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries
                .Where(item => item.Path != PathFor(entry, "residual-open"))
                .Append(RawRepositoryEntry.FromText(PathFor(entry), text)));
            loaded = Assert.Single(BackfillInventoryLoader.Load(Decode(raw)).RequireDigestionEntries());
        }
        Assert.Equal(text, Encoding.UTF8.GetString((legacyEntry
            ? BackfillInventoryWriter.WriteEntry(loaded) : BackfillInventoryWriter.WriteAtom(loaded)).AsSpan()));
        return loaded;
    }

    [Theory]
    [InlineData("mul_comm", true)]
    [InlineData("Nat.fib_dvd", true)]
    [InlineData("add_comm", true)]
    [InlineData("_root_name2'", true)]
    [InlineData("α₁'.β₂′!?", true)]
    [InlineData("get!", true)]
    [InlineData("Array.get?", true)]
    [InlineData("", false)]
    [InlineData(".foo", false)]
    [InlineData("foo.", false)]
    [InlineData("a..b", false)]
    [InlineData("a b", false)]
    [InlineData("0foo", false)]
    [InlineData("Nat.0foo", false)]
    public void UpstreamDeclarationNamesAcceptRootAndQualifiedIdentifiers(string name, bool accepted)
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = fixture.Ledger.RequireDigestionEntries().Single();
        var receipt = Settled(entry).Receipts.Upstream! with { Declarations = [name] };
        Assert.Equal(accepted, receipt.IsValid);
        var yaml = Receipt().Replace("Nat.add_comm", "'" + name + "'", StringComparison.Ordinal);
        if (accepted)
            Assert.Equal(name, Assert.Single(Settled(entry, yaml).Receipts.Upstream!.Declarations));
        else
            Assert.Throws<FormatException>(() => Settled(entry, yaml));
    }

    [Theory]
    [InlineData("justification", "'   '", "must be a nonempty scalar")]
    [InlineData("declarations", "\n      - Nat..bad", "must be a non-empty ordinal-sorted distinct list of Lean declaration names")]
    [InlineData("mathlib_rev", "bad-rev", "must be 40 lowercase hexadecimal characters")]
    [InlineData("probe_sha256", "bad-sha", "must be sha256: followed by 64 lowercase hexadecimal characters")]
    [InlineData("probe_axioms", "\n      - sorryAx", "must be an ordinal-sorted distinct list drawn from Classical.choice, Quot.sound, propext")]
    [InlineData("previous_atom_id", "bad-id", "must be a 64-character lowercase hexadecimal atom id or null")]
    [InlineData("next_atom_id", "bad-id", "must be a 64-character lowercase hexadecimal atom id or null")]
    public void UpstreamMalformedFieldDiagnosticsNameFieldAndShape(string field, string value, string expected)
    {
        AssertUpstreamFieldDiagnostic(field, value, expected);
    }

    [Theory]
    [InlineData("declarations", "[]")]
    [InlineData("declarations", "\n      - Nat.add_comm\n      - Nat.add_assoc")]
    [InlineData("declarations", "\n      - Nat.add_comm\n      - Nat.add_comm")]
    [InlineData("probe_axioms", "\n      - propext\n      - Classical.choice")]
    [InlineData("probe_axioms", "\n      - propext\n      - propext")]
    public void UpstreamListDiagnosticsExplainOrderingAndDistinctness(string field, string value)
    {
        AssertUpstreamFieldDiagnostic(field, value, field == "declarations"
            ? "must be a non-empty ordinal-sorted distinct list of Lean declaration names"
            : "must be an ordinal-sorted distinct list drawn from Classical.choice, Quot.sound, propext");
    }

    private static void AssertUpstreamFieldDiagnostic(string field, string value, string expected)
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = fixture.Ledger.RequireDigestionEntries().Single();
        var lines = Receipt().Split('\n').ToList();
        var index = lines.FindIndex(line => line.StartsWith("    " + field + ":", StringComparison.Ordinal));
        lines.RemoveRange(index, field == "declarations" ? 2 : 1);
        lines.Insert(index, "    " + field + ": " + value);
        var error = Assert.Throws<FormatException>(() => Settled(entry, string.Join('\n', lines)));
        Assert.Contains($"entry {entry.AtomId} upstream receipt: {field} {expected}", error.Message, StringComparison.Ordinal);
    }
}
