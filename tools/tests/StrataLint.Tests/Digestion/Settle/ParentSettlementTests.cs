using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.NonpropositionalTestSupport;

namespace StrataLint.Tests;

public sealed class ParentSettlementTests
{
    private const string ParentText = DecomposeFixture.Bold + "\n";
    private const string Before = "**Theorem 2.1** Preceding assertion.\n\n";
    private const string After = "**Theorem 3.1** Following assertion.\n\n";

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ExplicitParentUsesWholeSpanOutsideNeighborsAndOneAtomicUpdate(bool nested)
    {
        var fixture = Create(nested);
        var parent = Target(fixture);
        var context = DigestionAtomContextProjection.Resolve(fixture.Snapshot, fixture.Document, parent.AtomId);
        Assert.Equal(DecomposeFixture.Entry(Before).AtomId, context.Previous!.Value.AtomId);
        Assert.Equal(DecomposeFixture.Entry(After).AtomId, context.Next!.Value.AtomId);
        Assert.Equal(Encoding.UTF8.GetBytes(ParentText), context.Current.RawBytes.ToArray());
        Assert.Equal((2, 3), (context.Index, context.Count));
        using var temporary = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, fixture.Current);
        var calls = 0;
        var before = fixture.Current;
        var result = SettleAtomCommandTests.Run(temporary.Path, before, Request(parent.AtomId,
            DecomposeFixture.Entry(Before).AtomId, DecomposeFixture.Entry(After).AtomId), apply: (root, current, updates) =>
        {
            calls++;
            Assert.Equal(2, updates.Length);
            Assert.All(updates, update => Assert.EndsWith("/" + parent.AtomId + ".yaml", update.Path, StringComparison.Ordinal));
            IngestCommand.ApplyLedgerUpdatesAtomically(root, current, updates);
        });
        Assert.True(result.Success, result.Error);
        Assert.Equal(1, calls);
        fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);
        AssertUnchangedExcept(before, fixture.Current, parent.AtomId);
        Assert.Equal(parent.Receipts.ChainAtoms.ToArray(), Target(fixture).Receipts.ChainAtoms.ToArray());
        Assert.Equal(State, StateName(Target(fixture).ProjectedStatus));
        var clear = SettleAtomCommandTests.Run(temporary.Path, fixture.Current, "", ["--clear", parent.AtomId, "--base", "baseline"]);
        Assert.True(clear.Success, clear.Error);
        fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);
        Assert.Equal(before.Entries.Select(e => (e.Path, Convert.ToHexString(e.Bytes.AsSpan()))).OrderBy(e => e.Path),
            fixture.Current.Entries.Select(e => (e.Path, Convert.ToHexString(e.Bytes.AsSpan()))).OrderBy(e => e.Path));
    }

    [Theory]
    [InlineData("open", "CHAIN_INCOMPLETE")]
    [InlineData("unresolved", "CHAIN_INCOMPLETE")]
    [InlineData("forged-terminal", "CHAIN_INCOMPLETE")]
    [InlineData("missing-entry", "OCCURRENCE_MISSING")]
    [InlineData("missing-cas", "INFRASTRUCTURE")]
    [InlineData("missing-parent-cas", "INFRASTRUCTURE")]
    [InlineData("corrupt-parent-cas", "INFRASTRUCTURE")]
    [InlineData("corrupt-cas", "INFRASTRUCTURE")]
    [InlineData("identity", "OCCURRENCE_MISSING")]
    [InlineData("overlap", "OCCURRENCE_MISSING")]
    [InlineData("reordered", "OCCURRENCE_MISSING")]
    [InlineData("nested-open", "CHAIN_INCOMPLETE")]
    [InlineData("nested-corrupt", "OCCURRENCE_MISSING")]
    [InlineData("wrong-descendant-context", "CONTEXT_MISMATCH")]
    [InlineData("wrong-parent-context", "CONTEXT_MISMATCH")]
    [InlineData("missing-occurrence", "OCCURRENCE_MISSING")]
    [InlineData("duplicate-entry", "OCCURRENCE_MISSING")]
    public void InvalidDescendantOrContextFailsBeforeWrites(string fault, string code)
    {
        var fixture = Create(fault.StartsWith("nested", StringComparison.Ordinal));
        var parent = Target(fixture);
        var child = fixture.Document.RequireDigestionEntries().First(entry => entry.AtomId != parent.AtomId
            && entry.Receipts.ChainAtoms.IsEmpty);
        var request = Request(parent.AtomId, DecomposeFixture.Entry(Before).AtomId, DecomposeFixture.Entry(After).AtomId);
        switch (fault)
        {
            case "open": case "nested-open": case "forged-terminal": case "unresolved":
                fixture.Replace(child with
                {
                    Receipts = child.Receipts with { Nonpropositional = null,
                        UnresolvedSubitems = fault == "unresolved" ? ["unresolved obligation"] : [] },
                    ProjectedStatus = fault == "forged-terminal" ? child.ProjectedStatus
                        : new(DigestionMigrationState.Residual, DigestionTruthState.Open),
                });
                break;
            case "wrong-descendant-context":
                fixture.Replace(child with { Receipts = child.Receipts with
                { Nonpropositional = child.Receipts.Nonpropositional! with { NextAtomId = new string('f', 64) } } });
                break;
            case "identity":
                fixture.Replace(child with { Fingerprints = child.Fingerprints with { NormalizedSha256 = "sha256:" + new string('f', 64) } });
                break;
            case "overlap": case "reordered":
                fixture.Replace(parent with { Receipts = parent.Receipts with
                { ChainAtoms = fault == "overlap" ? [parent.Receipts.ChainAtoms[0], parent.Receipts.ChainAtoms[0]]
                    : parent.Receipts.ChainAtoms.Reverse().ToImmutableArray() } });
                break;
            case "missing-entry":
                fixture.Current = RawRepositorySnapshot.Create(fixture.Current.Entries.Where(e => e.Path != PathFor(child)));
                break;
            case "missing-parent-cas":
                fixture.Current = RawRepositorySnapshot.Create(fixture.Current.Entries.Where(e => e.Path != DigestionCasStore.RootPath + parent.AtomId));
                break;
            case "corrupt-parent-cas":
                ReplaceFile(fixture, DigestionCasStore.RootPath + parent.AtomId, "corrupted parent bytes\n");
                break;
            case "missing-cas":
                fixture.Current = RawRepositorySnapshot.Create(fixture.Current.Entries.Where(e => e.Path != DigestionCasStore.RootPath + child.AtomId));
                break;
            case "corrupt-cas": case "nested-corrupt":
                ReplaceFile(fixture, DigestionCasStore.RootPath + child.AtomId, "corrupted bytes\n");
                break;
            case "wrong-parent-context":
                request = Request(parent.AtomId, parent.Receipts.ChainAtoms[0], DecomposeFixture.Entry(After).AtomId);
                break;
            case "missing-occurrence":
                ReplaceFile(fixture, "docs/probe.md", Before + After);
                break;
            case "duplicate-entry":
                fixture.Current = RawRepositorySnapshot.Create(fixture.Current.Entries.Append(new RawRepositoryEntry(
                    PathFor(child, "residual-open"), BackfillInventoryWriter.WriteAtom(child))));
                break;
        }
        using var temporary = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, fixture.Current);
        var before = SettleAtomCommandTests.Image(temporary);
        var calls = 0;
        var result = SettleAtomCommandTests.Run(temporary.Path, fixture.Current, request, apply: (_, _, _) => calls++);
        Assert.False(result.Success);
        Assert.StartsWith("SETTLE_INVALID " + code, result.Error, StringComparison.Ordinal);
        Assert.Equal(0, calls);
        Assert.Equal(before, SettleAtomCommandTests.Image(temporary));
    }

    [Theory]
    [InlineData(false, 5, 6)]
    [InlineData(true, 6, 7)]
    public void RepeatedParentKeepsLeafMembershipAndRequiresOccurrenceIndex(bool nested, int secondIndex, int count)
    {
        var fixture = Create(nested, repeated: true);
        var parent = Target(fixture);
        var stream = DigestionAtomContextProjection.MaterializeSource(fixture.Snapshot, fixture.Document, parent.SourceId);
        Assert.DoesNotContain(parent.AtomId, stream.AtomIds);
        var contexts = stream.ResolveOccurrences(parent.AtomId);
        Assert.Equal(2, contexts.Length);
        Assert.Equal(new[] { 2, secondIndex }, contexts.Select(c => c.Index));
        Assert.All(contexts, context => Assert.Equal(count, context.Count));
        Assert.Equal(DecomposeFixture.Entry(Before).AtomId, contexts[0].Previous!.Value.AtomId);
        Assert.Equal(DecomposeFixture.Entry(After).AtomId, contexts[0].Next!.Value.AtomId);
        Assert.Equal(DecomposeFixture.Entry(After).AtomId, contexts[1].Previous!.Value.AtomId);
        Assert.Equal(DecomposeFixture.Entry(Before).AtomId, contexts[1].Next!.Value.AtomId);
        using var temporary = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, fixture.Current);
        var request = Request(parent.AtomId, DecomposeFixture.Entry(After).AtomId, DecomposeFixture.Entry(Before).AtomId);
        foreach (var (suffix, code) in new[] { ("", "OCCURRENCE_INDEX_REQUIRED"), ("occurrence_index = 3\n", "OCCURRENCE_INDEX_INVALID"),
                     ("occurrence_index = 1\n", "CONTEXT_MISMATCH") })
        {
            var result = SettleAtomCommandTests.Run(temporary.Path, fixture.Current, request + suffix);
            Assert.StartsWith("SETTLE_INVALID " + code, result.Error, StringComparison.Ordinal);
        }
        var success = SettleAtomCommandTests.Run(temporary.Path, fixture.Current, request + "occurrence_index = 2\n");
        Assert.True(success.Success, success.Error);
    }

    internal static DecomposeFixture Create(bool nested = false, bool repeated = false)
    {
        var fixture = new DecomposeFixture(ParentText);
        var decomposed = DecomposeAtomCommand.Run("synthetic", fixture.Gateway, fixture.Args(), fixture.Apply);
        Assert.True(decomposed.Success, decomposed.Error);
        if (nested)
        {
            var child = Target(fixture).Receipts.ChainAtoms[0];
            var result = DecomposeAtomCommand.Run("synthetic", fixture.Gateway,
                [.. fixture.Args(child), "--split-at", "16"], fixture.Apply);
            Assert.True(result.Success, result.Error);
        }
        ReplaceFile(fixture, "docs/probe.md", Before + ParentText + After
            + (repeated ? ParentText + Before : ""));
        using var temporary = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, fixture.Current);
        var order = fixture.Document.RequireDigestionEntries().Where(e => e.AtomId != fixture.Parent.AtomId)
            .OrderBy(e => fixture.Current.Entries.Single(raw => raw.Path == DigestionCasStore.RootPath + e.AtomId).Bytes.Length).ToArray();
        foreach (var entry in order)
        {
            var contexts = DigestionAtomContextProjection.ResolveOccurrences(fixture.Snapshot, fixture.Document, entry.AtomId);
            var context = contexts[0];
            var request = Request(entry.AtomId, context.Previous?.AtomId, context.Next?.AtomId)
                + (contexts.Length > 1 ? "occurrence_index = 1\n" : "");
            var settled = SettleAtomCommandTests.Run(temporary.Path, fixture.Current, request);
            Assert.True(settled.Success, settled.Error);
            fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);
        }
        return fixture;
    }

    internal static DigestionLedgerEntry Target(DecomposeFixture fixture) =>
        fixture.Document.RequireDigestionEntries().Single(e => e.AtomId == fixture.Parent.AtomId);

    internal static string Request(string id, string? previous, string? next) =>
        $"atom_id = '{id}'\njustification = 'Upstream declarations close every clause; no project GID is available.'\n"
        + $"previous_atom_id = '{previous ?? "source-boundary"}'\nnext_atom_id = '{next ?? "source-boundary"}'\n";

    internal static void ReplaceFile(DecomposeFixture fixture, string path, string text) =>
        fixture.Current = RawRepositorySnapshot.Create(fixture.Current.Entries.Where(e => e.Path != path)
            .Append(RawRepositoryEntry.FromText(path, text)));

    private static void AssertUnchangedExcept(RawRepositorySnapshot before, RawRepositorySnapshot after, string id)
    {
        Assert.Equal(before.Entries.Length, after.Entries.Length);
        foreach (var file in before.Entries.Where(e => !e.Path.EndsWith("/" + id + ".yaml", StringComparison.Ordinal)))
            Assert.Equal(file.Bytes.ToArray(), after.Entries.Single(e => e.Path == file.Path).Bytes.ToArray());
    }
}
