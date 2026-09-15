using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.UpstreamTestSupport;

namespace StrataLint.Tests;

public sealed class Sl016UpstreamTests
{
    [Theory]
    [InlineData("missing", "entry", true)]
    [InlineData("mismatch", "entry", true)]
    [InlineData("valid", "entry", false)]
    [InlineData("missing", "probe", true)]
    [InlineData("mismatch", "probe", true)]
    [InlineData("missing", "unrelated", false)]
    [InlineData("mismatch", "unrelated", false)]
    public void UpstreamProbeBindingIsFailClosedAndDeltaScoped(string value, string changed, bool blocked)
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = Settled(fixture.Ledger.RequireDigestionEntries().Single());
        fixture = fixture.WithEntries([entry]);
        var baseline = Decode(WithCas(fixture));
        var files = WithCas(fixture).Entries.Where(item => item.Path != ProbePath(entry));
        if (value != "missing") files = files.Append(RawRepositoryEntry.FromText(ProbePath(entry), value == "valid" ? Probe : "changed\r\n"));
        var current = Decode(RawRepositorySnapshot.Create(files));
        var changes = RawChangeSet.CreateWithKinds([(changed == "entry" ? PathFor(entry) : changed == "probe" ? ProbePath(entry) : "README.md",
            value == "missing" && changed == "probe" ? RawChangeKind.Deleted : RawChangeKind.Modified)]);
        var evaluation = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.ChangedSet,
            fixture.Ledger, current, DigestionTestSupport.AcceptedLean(Array.Empty<string>()),
            baselineDocument: fixture.Ledger, baselineSnapshot: baseline, changes: changes);
        var findings = BackfillInventoryRule.ClassifyReceiptIntegrityGaps(evaluation)
            .Where(item => item.Message.Contains("BACKFILL_UPSTREAM_PROBE", StringComparison.Ordinal)).ToArray();
        Assert.Equal(blocked ? 1 : 0, findings.Length);
        if (blocked)
        {
            Assert.Equal(AdmissionEffect.Block, findings[0].Effect);
            Assert.Contains(value == "missing" ? ":missing" : ":sha256 mismatch stored=", findings[0].Message, StringComparison.Ordinal);
            if (value == "mismatch") Assert.Contains("actual=" + DigestionFingerprint.Compute(Encoding.UTF8.GetBytes("changed\r\n")).RawSha256,
                findings[0].Message, StringComparison.Ordinal);
            Assert.True(evaluation.HasReceiptIntegrityFailure);
        }
    }

    [Fact]
    public void UpstreamProbeChangeWakesSl016()
    {
        var fixture = new RuleFixture();
        var path = "Meta/Digestion/upstream/" + new string('a', 64) + ".lean";
        Assert.True(BackfillInventoryRule.IsAffectedBy(fixture.Build(RawChangeSet.Create([path]))));
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void UpstreamProbeDependencyUsesChangedBytes(bool changed)
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = Settled(fixture.Ledger.RequireDigestionEntries().Single());
        fixture = fixture.WithEntries([entry]);
        var baseline = Decode(WithCas(fixture));
        var current = Decode(RawRepositorySnapshot.Create(WithCas(fixture).Entries.Select(item =>
            changed && item.Path == ProbePath(entry) ? RawRepositoryEntry.FromText(item.Path, "changed") : item)));
        var impact = BackfillDeltaImpactResolver.Resolve(current, baseline, null, fixture.Ledger,
            RawChangeSet.Create([ProbePath(entry)]));
        Assert.Equal(changed, DigestionCasStore.EntryChanged(entry, impact.EvaluationChanges));
    }

    [Theory]
    [InlineData("invalid")]
    [InlineData("coverage")]
    [InlineData("quarantine")]
    [InlineData("disposition")]
    [InlineData("nonpropositional")]
    [InlineData("unresolved")]
    public void UpstreamInvalidOrConflictingInMemoryReceiptIsFinding(string conflict)
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = Settled(fixture.Ledger.RequireDigestionEntries().Single());
        entry = conflict switch
        {
            "invalid" => entry with { Receipts = entry.Receipts with { Upstream = entry.Receipts.Upstream! with { MathlibRev = "bad" } } },
            "coverage" => entry with { Coverage = [new("D5/S0/Carrier/Probe", null)] },
            "quarantine" => entry with { Receipts = entry.Receipts with { Quarantine = new("reason", "condition", "already-covered") } },
            "disposition" => entry with { Receipts = entry.Receipts with { CoverDisposition = new(new(DigestionMigrationState.Partial, DigestionTruthState.Closed), [], []) } },
            "nonpropositional" => entry with { Receipts = entry.Receipts with { Nonpropositional = new("reason", null, null) } },
            _ => entry with { Receipts = entry.Receipts with { UnresolvedSubitems = ["pending"] } },
        };
        fixture = fixture.WithEntries([entry]);
        var evaluation = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan,
            fixture.Ledger, Decode(WithCas(fixture)), DigestionTestSupport.AcceptedLean(Array.Empty<string>()));
        Assert.Contains($"entry {entry.AtomId} upstream receipt is invalid or conflicts with live obligations", evaluation.Findings);
        Assert.NotEqual("upstream-closed", StateName(Assert.Single(evaluation.Entries).DerivedStatus));
    }
}
