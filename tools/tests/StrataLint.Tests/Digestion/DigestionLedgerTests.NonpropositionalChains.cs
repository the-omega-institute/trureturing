using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;
using static StrataLint.Tests.NonpropositionalTestSupport;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
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
            gid, new(gid, TestModuleStatementId), new(gid, record.DefinitionSha256, record.EmissionSha256),
            atomizer: AtomizerRegistry.NoAtomizerId).RequireDigestionEntries()) with { SourceId = "source" };
        var childIds = Enumerable.Range(1, 5).Select(index => new string((char)('a' + index), 64)).ToImmutableArray();
        var children = childIds.Select((id, index) => (index < 2 ? complete : settled) with { AtomId = id }).ToArray();
        var parent = complete with { AtomId = new string('a', 64), Coverage = [],
            Receipts = complete.Receipts with { Scribe = [], ChainAtoms = childIds },
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
                AcceptedLean(targetPath), VerifiedScribeEmissions.Create([record]), baselineDocument: document)
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
                    Receipts = new([], mode == "partial" ? ["live"] : [], [], null) });
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
