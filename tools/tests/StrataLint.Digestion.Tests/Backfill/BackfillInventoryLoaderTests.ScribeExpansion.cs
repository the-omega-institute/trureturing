using StrataLint.Engine;

namespace StrataLint.Digestion.Tests;

public sealed partial class BackfillInventoryLoaderTests
{
    [Fact]
    public void DirectoryAtomWithoutTheRetiredScribeKeyLoadsAndEvaluates()
    {
        var snapshot = ScribeOptionalSnapshot();
        var document = BackfillInventoryLoader.Load(snapshot);
        var baseline = BackfillInventoryLoader.LoadBaseline(snapshot);

        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan, document, snapshot,
            DigestionTestSupport.AcceptedLean(Array.Empty<string>()), baselineDocument: baseline);

        Assert.Empty(evaluation.Findings);
        var status = Assert.Single(evaluation.Entries);
        Assert.Equal(new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open),
            status.DerivedStatus);
    }

    [Theory]
    [InlineData("quarantine")]
    [InlineData("cover_disposition")]
    [InlineData("nonpropositional")]
    [InlineData("chain_atoms")]
    public void LiveReceiptsStillLoadAndEvaluateAfterTheScribeKeyRetired(string field)
    {
        var receipt = field switch
        {
            "quarantine" => "  quarantine:\n    justification: missing premise\n"
                + "    reentry_condition: prove premise\n    blocker_class: missing-prerequisite\n",
            "cover_disposition" => "  cover_disposition:\n    outcome: partial-open\n"
                + "    gids:\n      - D5/S0/Carrier/Probe.probe\n    gaps: []\n",
            "nonpropositional" => "  nonpropositional:\n    justification: introductory prose\n"
                + "    previous_atom_id: null\n    next_atom_id: null\n",
            "chain_atoms" => "  chain_atoms:\n    - missing-child\n",
            _ => throw new ArgumentOutOfRangeException(nameof(field)),
        };
        var state = field == "nonpropositional" ? "nonpropositional-inapplicable" : "residual-open";
        var without = ScribeOptionalSnapshot(receipt, state: state);
        var document = BackfillInventoryLoader.Load(without);
        var entry = Assert.Single(document.RequireDigestionEntries());
        var baselineEntry = Assert.Single(BackfillInventoryLoader.LoadBaseline(without).RequireDigestionEntries());
        Assert.Equal(BackfillInventoryWriter.WriteAtom(entry).ToArray(),
            BackfillInventoryWriter.WriteAtom(baselineEntry).ToArray());
        switch (field)
        {
            case "quarantine":
                Assert.Equal(new DigestionQuarantine("missing premise", "prove premise", "missing-prerequisite"),
                    entry.Receipts.Quarantine);
                break;
            case "cover_disposition":
                Assert.Equal(new DigestionStatus(DigestionMigrationState.Partial, DigestionTruthState.Open),
                    entry.Receipts.CoverDisposition!.Outcome);
                Assert.Equal(["D5/S0/Carrier/Probe.probe"], entry.Receipts.CoverDisposition.Gids.ToArray());
                Assert.Empty(entry.Receipts.CoverDisposition.Gaps);
                break;
            case "nonpropositional":
                Assert.Equal("introductory prose", entry.Receipts.Nonpropositional!.Justification);
                Assert.Null(entry.Receipts.Nonpropositional.PreviousAtomId);
                Assert.Null(entry.Receipts.Nonpropositional.NextAtomId);
                break;
            case "chain_atoms":
                Assert.Equal(["missing-child"], entry.Receipts.ChainAtoms.ToArray());
                break;
        }

        var evaluation = EvaluateScribeOptional(without);
        Assert.Empty(evaluation.Findings);
        var status = Assert.Single(evaluation.Entries);
        Assert.Equal(new DigestionStatus(
            field == "nonpropositional" ? DigestionMigrationState.Nonpropositional : DigestionMigrationState.Residual,
            field == "nonpropositional" ? DigestionTruthState.Inapplicable : DigestionTruthState.Open),
            status.DerivedStatus);
        Assert.False(status.Deletable);
        if (field == "chain_atoms")
            Assert.Contains(status.Gaps, gap => gap.Code == "chain-migration-incomplete" && gap.Detail == "missing-child");
    }

    [Theory]
    [InlineData("gid")]
    [InlineData("target_statement_id")]
    public void CoverageEdgeKeyContractSurvivesTheScribeKeyRetirement(string key)
    {
        const string coverage = "coverage_gids:\n  - gid: D5/S0/Carrier/Probe.probe\n    target_statement_id: null\n";
        var snapshot = ScribeOptionalSnapshot(coverage: coverage, state: "partial-open");
        foreach (var baseline in new[] { false, true })
        {
            var document = baseline ? BackfillInventoryLoader.LoadBaseline(snapshot) : BackfillInventoryLoader.Load(snapshot);
            var edge = Assert.Single(Assert.Single(document.RequireDigestionEntries()).Coverage);
            Assert.Equal("D5/S0/Carrier/Probe.probe", edge.Gid);
            Assert.Null(edge.TargetStatementId);
            var invalid = key == "gid"
                ? "coverage_gids:\n  - target_statement_id: null\n"
                : "coverage_gids:\n  - gid: D5/S0/Carrier/Probe.probe\n";
            var error = Assert.Throws<FormatException>(() => baseline
                ? BackfillInventoryLoader.LoadBaseline(ScribeOptionalSnapshot(coverage: invalid))
                : BackfillInventoryLoader.Load(ScribeOptionalSnapshot(coverage: invalid)));
            Assert.Contains("coverage edge keys are not canonical", error.Message, StringComparison.Ordinal);
        }
        var status = Assert.Single(EvaluateScribeOptional(snapshot).Entries);
        Assert.Equal(DigestionTruthState.Open, status.DerivedStatus.Truth);
        Assert.False(status.Deletable);
    }

    [Theory]
    [InlineData("  quarantine:\n    justification: missing premise\n    reentry_condition: retry\n    blocker_class: unknown\n", "quarantine blocker_class")]
    [InlineData("  cover_disposition:\n    outcome: invalid\n    gids: []\n    gaps: []\n", "cover_disposition outcome")]
    [InlineData("  nonpropositional:\n    justification: prose\n    previous_atom_id: null\n", "nonpropositional keys are not canonical")]
    [InlineData("  chain_atoms: null\n", "chain_atoms must be a list")]
    public void InvalidLiveReceiptsAreStillRejected(string receipt, string expected)
    {
        Assert.Single(BackfillInventoryLoader.Load(ScribeOptionalSnapshot()).RequireDigestionEntries());
        foreach (var baseline in new[] { false, true })
        {
            var snapshot = ScribeOptionalSnapshot(receipt);
            var error = Assert.Throws<FormatException>(() => baseline
                ? BackfillInventoryLoader.LoadBaseline(snapshot) : BackfillInventoryLoader.Load(snapshot));
            Assert.Contains(expected, error.Message, StringComparison.Ordinal);
        }
    }

    [Theory]
    [InlineData("  scribe: []\n")]
    [InlineData("  scribe: null\n")]
    [InlineData("  scribe:\n    - gid: D5/S0/Carrier/Probe\n      definition_sha256: sha256:a\n      emission_sha256: sha256:b\n")]
    [InlineData("  unrelated: []\n")]
    public void TheRetiredScribeKeyIsRejectedInEveryShape(string receipt)
    {
        // Owner ruling #5942 retired Scribe byte receipts; #6323 through #6331 removed the
        // last committed key. The loader now has no such key, so any entry carrying one is
        // an unknown key and must fail closed rather than be parsed and ignored.
        Assert.Single(BackfillInventoryLoader.Load(ScribeOptionalSnapshot()).RequireDigestionEntries());
        foreach (var baseline in new[] { false, true })
        {
            var snapshot = ScribeOptionalSnapshot(receipt);
            var error = Assert.Throws<FormatException>(() => baseline
                ? BackfillInventoryLoader.LoadBaseline(snapshot)
                : BackfillInventoryLoader.Load(snapshot));
            Assert.Contains("receipts keys are not canonical", error.Message, StringComparison.Ordinal);
        }
    }

    private static DigestionLedgerEvaluation EvaluateScribeOptional(RepositorySnapshot snapshot) =>
        DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan,
            BackfillInventoryLoader.Load(snapshot), snapshot, DigestionTestSupport.AcceptedLean(Array.Empty<string>()));

    private static RepositorySnapshot ScribeOptionalSnapshot(
        string receipt = "", string coverage = "coverage_gids: []\n",
        string state = "residual-open")
    {
        const string content = "introductory prose";
        var atom = Atom("delta-v0.1", state, "delta", content);
        var text = atom.Text.Replace("coverage_gids: []\n", coverage, StringComparison.Ordinal)
            .Replace("  chain_atoms: []\n", "", StringComparison.Ordinal) + receipt;
        return Snapshot(Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, text), (DigestionCasStore.RootPath + FixtureAtomId(content), content));
    }
}
