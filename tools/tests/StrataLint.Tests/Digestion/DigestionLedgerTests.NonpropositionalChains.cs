using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;
using static StrataLint.Tests.NonpropositionalTestSupport;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
    [Fact]
    public void ExplicitUpstreamParentRequiresOwnReceiptAndReopensAfterDescendantClear()
    {
        const string statement = "**Theorem 1.1** For every natural number n, n + 0 = n.\n\n";
        const string proof = "**Proof** Apply Nat.add_zero to n.\n";
        const string justification = "All clauses follow from Nat.add_zero; no frozen project GID is available.";
        var fixture = new DecomposeFixture(statement + proof);
        var originalContext = DigestionAtomContextProjection.Resolve(
            fixture.Snapshot, fixture.Document, fixture.Parent.AtomId);
        Assert.Null(originalContext.Previous);
        Assert.Null(originalContext.Next);
        var decomposition = DecomposeAtomCommand.Run("synthetic", fixture.Gateway,
            [.. fixture.Args(), "--split-at", Encoding.UTF8.GetByteCount(statement)
                .ToString(System.Globalization.CultureInfo.InvariantCulture)], fixture.Apply);
        Assert.True(decomposition.Success, decomposition.Error);
        var parent = fixture.Document.RequireDigestionEntries().Single(entry => entry.AtomId == fixture.Parent.AtomId);
        var children = parent.Receipts.ChainAtoms;
        Assert.Equal(2, children.Length);
        Assert.Equal(Encoding.UTF8.GetBytes(statement + proof), children.SelectMany(id =>
            fixture.Current.Entries.Single(entry => entry.Path == DigestionCasStore.RootPath + id).Bytes).ToArray());
        using var temporary = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, fixture.Current);
        var parentBytes = BackfillInventoryWriter.WriteAtom(parent).ToArray();

        string Request(string id, string? previous, string? next) =>
            $"atom_id = '{id}'\njustification = '{justification}'\n"
            + $"previous_atom_id = '{previous ?? "source-boundary"}'\n"
            + $"next_atom_id = '{next ?? "source-boundary"}'\n";

        for (var index = 0; index < children.Length; index++)
        {
            // Expected neighbors come from the lossless two-clause source, not the context query.
            var request = Request(children[index], index == 0 ? null : children[0],
                index == 0 ? children[1] : null);
            var settled = SettleAtomCommandTests.Run(temporary.Path, fixture.Current, request);
            Assert.True(settled.Success, settled.Error);
            fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);
        }
        var evaluation = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan,
            fixture.Document, fixture.Snapshot, AcceptedLean(Array.Empty<string>()), baselineDocument: fixture.Document);
        Assert.Empty(evaluation.Findings);
        var evaluatedParent = evaluation.Entries.Single(item => item.Entry.AtomId == parent.AtomId);
        Assert.Equal("residual-open", StateName(evaluatedParent.DerivedStatus));
        Assert.Contains(evaluatedParent.Gaps, gap => gap.Code == "coverage-gid-missing");
        Assert.DoesNotContain(evaluatedParent.Gaps, gap => gap.Code == "chain-migration-incomplete");
        Assert.All(evaluation.Entries.Where(item => children.Contains(item.Entry.AtomId)), item =>
            Assert.Equal(State, StateName(item.DerivedStatus)));
        Assert.Equal(parentBytes, fixture.Current.Entries.Single(entry => entry.Path == PathFor(parent)).Bytes.ToArray());
        var stream = DigestionAtomContextProjection.MaterializeSource(fixture.Snapshot, fixture.Document, parent.SourceId);
        Assert.Equal(children.ToArray(), stream.AtomIds.ToArray());
        var parentContext = Assert.Single(stream.ResolveOccurrences(parent.AtomId));
        Assert.Equal(Encoding.UTF8.GetBytes(statement + proof), parentContext.Current.RawBytes.ToArray());
        Assert.Null(parentContext.Previous);
        Assert.Null(parentContext.Next);
        Assert.Equal((1, 1), (parentContext.Index, parentContext.Count));

        var result = SettleAtomCommandTests.Run(temporary.Path, fixture.Current,
            Request(parent.AtomId, originalContext.Previous?.AtomId, originalContext.Next?.AtomId));
        Assert.True(result.Success, result.Error);
        fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);
        evaluation = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan,
            fixture.Document, fixture.Snapshot, AcceptedLean(Array.Empty<string>()), baselineDocument: fixture.Document);
        Assert.Empty(evaluation.Findings);
        Assert.Equal(State, StateName(evaluation.Entries.Single(item => item.Entry.AtomId == parent.AtomId).DerivedStatus));

        var clearParent = SettleAtomCommandTests.Run(temporary.Path, fixture.Current, "",
            ["--clear", parent.AtomId, "--base", "baseline"]);
        Assert.True(clearParent.Success, clearParent.Error);
        fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);
        Assert.Equal(parentBytes, fixture.Current.Entries.Single(entry => entry.Path == PathFor(parent)).Bytes.ToArray());
        result = SettleAtomCommandTests.Run(temporary.Path, fixture.Current, Request(parent.AtomId, null, null));
        Assert.True(result.Success, result.Error);
        fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);

        // A cleared child must restore its own obligation without changing its parent or sibling.
        var closedSnapshot = fixture.Current;
        var clear = SettleAtomCommandTests.Run(temporary.Path, fixture.Current, "",
            ["--clear", children[0], "--base", "baseline"]);
        Assert.True(clear.Success, clear.Error);
        Assert.Contains("SETTLE_ALIGN_REQUIRED ancestors=" + parent.AtomId, clear.Output, StringComparison.Ordinal);
        fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);
        foreach (var entry in closedSnapshot.Entries.Where(entry =>
                     !entry.Path.EndsWith("/" + children[0] + ".yaml", StringComparison.Ordinal)))
            Assert.Equal(entry.Bytes.ToArray(), fixture.Current.Entries.Single(current => current.Path == entry.Path).Bytes.ToArray());
        var clearedChild = fixture.Document.RequireDigestionEntries().Single(entry => entry.AtomId == children[0]);
        Assert.Null(clearedChild.Receipts.Nonpropositional);
        Assert.Equal("residual-open", StateName(clearedChild.ProjectedStatus));
        evaluation = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan,
            fixture.Document, fixture.Snapshot, AcceptedLean(Array.Empty<string>()), baselineDocument: fixture.Document);
        Assert.Contains(evaluation.Findings, finding => finding.Contains("entry " + parent.AtomId + " handwritten status", StringComparison.Ordinal));
        evaluatedParent = evaluation.Entries.Single(item => item.Entry.AtomId == parent.AtomId);
        Assert.Equal("partial-open", StateName(evaluatedParent.DerivedStatus));
        Assert.Contains(evaluatedParent.Gaps, gap => gap.Code == "chain-migration-incomplete" && gap.Detail == children[0]);
    }

    [Fact]
    public void NonpropositionalChildClosesBothChainPredicates()
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var atom = fixture.Atomized.Claims.Single();
        var settled = Settled(fixture.Ledger.RequireDigestionEntries().Single());
        const string gid = "D5/S0/Carrier/Probe";
        const string targetPath = gid + ".lean";
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var record = new ScribeEmissionRecord(gid, ScribeEmissionAttestation.DefinitionPath(gid),
            DigestionFingerprint.Compute(definition).RawSha256, ScribeEmissionAttestation.EmissionPath(gid),
            DigestionFingerprint.Compute(emission).RawSha256);
        var complete = Assert.Single(Ledger(atom, DigestionMigrationState.Absorbed, DigestionTruthState.Closed,
            gid, new(gid, TestModuleStatementId),
            atomizer: AtomizerRegistry.NoAtomizerId).RequireDigestionEntries()) with { SourceId = "source" };
        var childIds = Enumerable.Range(1, 5).Select(index => new string((char)('a' + index), 64)).ToImmutableArray();
        var children = childIds.Select((id, index) => (index < 2 ? complete : settled) with { AtomId = id }).ToArray();
        var parent = complete with { AtomId = new string('a', 64), Coverage = [],
            Receipts = complete.Receipts with { ChainAtoms = childIds },
            ProjectedStatus = new(DigestionMigrationState.Residual, DigestionTruthState.Open) };
        var files = new List<(string Path, byte[] Bytes)>
        {
            CasFile(atom), (targetPath, Encoding.UTF8.GetBytes(Lean(gid))),
            (record.DefinitionPath, definition), (record.EmissionPath, emission),
        };
        files.AddRange(FrozenLedgerFiles(targetPath, "probe"));
        var snapshot = Snapshot(files.ToArray());
        DigestionEntryEvaluation EvaluateParent(DigestionLedgerEntry candidate, IEnumerable<DigestionLedgerEntry> dependencies)
        {
            var document = Document(AtomizerRegistry.NoAtomizerId, [candidate, .. dependencies]);
            return DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan, document, snapshot,
                AcceptedLean(targetPath), baselineDocument: document)
                .Entries.Single(item => item.Entry.AtomId == parent.AtomId);
        }
        var openParent = EvaluateParent(parent, children);
        Assert.Equal("residual-open", StateName(openParent.DerivedStatus));
        Assert.DoesNotContain(openParent.Gaps, gap => gap.Code == "chain-migration-incomplete");
        var locallyComplete = complete with { AtomId = parent.AtomId,
            Receipts = complete.Receipts with { ChainAtoms = childIds } };
        Assert.Equal("absorbed-closed", StateName(EvaluateParent(locallyComplete, children).DerivedStatus));
        foreach (var mode in new[] { "residual", "partial", "missing" })
        {
            var changed = mode == "missing" ? children.Skip(1) : children.Select((child, index) =>
                index != 0 ? child : child with { Coverage = mode == "residual" ? [] : child.Coverage,
                    Receipts = new(mode == "partial" ? ["live"] : [], [], null) });
            var outcome = EvaluateParent(parent, changed);
            Assert.Contains(outcome.Gaps, gap => gap.Code == "chain-migration-incomplete" && gap.Detail == childIds[0]);
        }
    }

    [Fact]
    public void IngestAndAlignPreserveNonpropositionalReceipt()
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = Settled(fixture.Ledger.RequireDigestionEntries().Single());
        fixture = fixture.WithEntries([entry]);
        var snapshot = Decode(WithCas(fixture));
        var plan = DigestionIngestor.Plan(fixture.Ledger, snapshot, fixture.Ledger);
        var preserved = Assert.Single(plan.Document.RequireDigestionEntries());
        Assert.Equal(BackfillInventoryWriter.WriteAtom(entry).ToArray(), BackfillInventoryWriter.WriteAtom(preserved).ToArray());
        Assert.Equal(State, StateName(preserved.ProjectedStatus));
        var aligned = DigestionCoverageTargetAligner.Align(plan.Document, snapshot, AcceptedLean(Array.Empty<string>()),
            new Dictionary<RepoPath, TruthState>());
        Assert.Equal(BackfillInventoryWriter.WriteAtom(entry).ToArray(),
            BackfillInventoryWriter.WriteAtom(Assert.Single(aligned.RequireDigestionEntries())).ToArray());
        var repeated = fixture.WithEntries([entry, entry with { AtomId = new string('a', 64) }]);
        Assert.Single(DigestionIngestor.Plan(repeated.Ledger, snapshot, fixture.Ledger).Document.RequireDigestionEntries());
        var other = Settled(AtomContextFixture.Entry(fixture.Atomized.Claims.Single()),
            Receipt().Replace(Reason, "Different judgment.", StringComparison.Ordinal)) with { AtomId = new string('a', 64) };
        var conflict = fixture.WithEntries([entry, other]);
        Assert.Contains("conflicting nonpropositional", Assert.Throws<FormatException>(() =>
            DigestionIngestor.Plan(conflict.Ledger, snapshot, fixture.Ledger)).Message, StringComparison.Ordinal);
    }
}
