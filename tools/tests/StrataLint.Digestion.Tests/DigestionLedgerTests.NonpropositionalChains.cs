using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.TestSupport.DigestionTestSupport;
using static StrataLint.TestSupport.NonpropositionalTestSupport;

namespace StrataLint.Digestion.Tests;

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
                AcceptedLean(targetPath))
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

}
