using System.Text;
using StrataLint.Engine;

namespace StrataLint.Digestion.Tests;

public sealed partial class BackfillInventoryLoaderTests
{
    [Fact]
    public void BaselineRepeatedReferenceMappingRetainsBothBucketRecords()
    {
        var first = Atom("delta-v0.1", "absorbed-closed", "parent", "theorem/parent");
        var second = Atom("delta-v0.1", "residual-open", "parent", "theorem/parent");
        var snapshot = Snapshot(Source("delta-v0.1", "docs/delta.md", "none"), first, second);

        var entries = BackfillInventoryLoader.LoadBaseline(snapshot).RequireDigestionEntries();

        Assert.Equal(2, entries.Length);
        Assert.All(entries, entry => Assert.Equal(FixtureAtomId("theorem/parent"), entry.AtomId));
        Assert.Equal(
            [DigestionMigrationState.Absorbed, DigestionMigrationState.Residual],
            entries.Select(entry => entry.ProjectedStatus.Migration).ToArray());
    }

    [Fact]
    public void BaselineRepeatedReferenceMappingProjectsChainWithoutDroppingRecords()
    {
        var parent = Atom("delta-v0.1", "residual-open", "parent", "theorem/parent");
        var child = Atom("delta-v0.1", "residual-open", "child", "theorem/child");
        var childText = child.Text.Replace("  chain_atoms: []\n",
            "  chain_atoms:\n    - legacy-parent\n", StringComparison.Ordinal);
        var root = BackfillInventoryLoader.RootPath + "delta-v0.1/";
        var document = BackfillInventoryLoader.LoadBaseline(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (root + "absorbed-closed/legacy-parent.yaml", parent.Text),
            (root + "residual-open/legacy-parent.yaml", parent.Text),
            (child.Path, childText)));

        Assert.Equal(3, document.RequireDigestionEntries().Length);
        var projectedChild = Assert.Single(document.RequireDigestionEntries(),
            entry => entry.AtomId == FixtureAtomId("theorem/child"));
        Assert.Equal([FixtureAtomId("theorem/parent")], projectedChild.Receipts.ChainAtoms.ToArray());
    }

    [Fact]
    public void BaselineConflictingReferenceMappingFailsClosed()
    {
        var first = Atom("delta-v0.1", "absorbed-closed", "first", "theorem/first");
        var second = Atom("delta-v0.1", "residual-open", "second", "theorem/second");
        var root = BackfillInventoryLoader.RootPath + "delta-v0.1/";
        var error = Assert.Throws<FormatException>(() => BackfillInventoryLoader.LoadBaseline(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (root + "absorbed-closed/legacy-atom.yaml", first.Text),
            (root + "residual-open/legacy-atom.yaml", second.Text))));

        Assert.Contains("ambiguous baseline atom reference: legacy-atom", error.Message, StringComparison.Ordinal);
        Assert.Contains(FixtureAtomId("theorem/first"), error.Message, StringComparison.Ordinal);
        Assert.Contains(FixtureAtomId("theorem/second"), error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CurrentCoverageEdgeLoadsForCandidateAndBaseline(bool baseline)
    {
        var atom = Atom("delta-v0.1", "partial-open", "delta-atom", "manual/delta");
        var withCoverage = atom.Text.Replace(
            "coverage_gids: []",
            "coverage_gids:\n  - gid: D5/X_Frontier/SyntheticSourceTarget\n"
                + "    target_statement_id: null",
            StringComparison.Ordinal);
        var snapshot = Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, withCoverage));
        var inventory = baseline
            ? BackfillInventoryLoader.LoadBaseline(snapshot)
            : BackfillInventoryLoader.Load(snapshot);

        Assert.Equal(
            ["D5/X_Frontier/SyntheticSourceTarget"],
            inventory.RequireReferencedGids().ToArray());
    }

    [Fact]
    public void LegacyCoverageTargetSha256KeyIsRejected()
    {
        var atom = Atom("delta-v0.1", "partial-open", "delta-atom", "manual/delta");
        var legacy = atom.Text.Replace(
            "coverage_gids: []",
            "coverage_gids:\n"
                + "  - gid: D5/S0/Carrier/Probe.probe\n"
                + "    target_sha256: sha256:1111111111111111111111111111111111111111111111111111111111111111",
            StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, legacy))));

        Assert.Contains("coverage edge keys are not canonical", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void BaselineCoverageProjectionRejectsHistoricalTargetField()
    {
        var atom = Atom("delta-v0.1", "partial-open", "delta-atom", "manual/delta");
        var historical = atom.Text.Replace(
            "coverage_gids: []",
            "coverage_gids:\n"
                + "  - gid: D5/S0/Carrier/Probe.probe\n"
                + "    historical_target_field: not-a-statement-identity",
            StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.LoadBaseline(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, historical))));

        Assert.Contains("coverage edge keys are not canonical", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void BaselineLegacyCoverageElementFailsClosed()
    {
        const string resolvedGid = "D5/S0/Carrier/Probe.resolved";
        var atom = CanonicalCoverageAtom("coverage_gids: []");
        var legacy = atom.Text
            .Replace(
                "coverage_gids: []\n",
                $"coverage_gids:\n  - {resolvedGid}\n",
                StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.LoadBaseline(Snapshot(
                Source("delta-v0.1", "docs/delta.md", "none"),
                (atom.Path, legacy))));

        Assert.Contains("coverage edge must be a mapping", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CandidateLegacyCoverageElementFailsClosed()
    {
        const string resolvedGid = "D5/S0/Carrier/Probe.resolved";
        var atom = CanonicalCoverageAtom("coverage_gids: []");
        var legacy = atom.Text
            .Replace(
                "coverage_gids: []\n",
                $"coverage_gids:\n  - {resolvedGid}\n",
                StringComparison.Ordinal);

        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, legacy))));

        Assert.Contains("coverage edge must be a mapping", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void BaselineLegacyCoverageSchemaRejectsAdditionalUnknownEntryKey()
    {
        var atom = CanonicalCoverageAtom("coverage_gids: []");
        var legacy = atom.Text + "historical_extra: ignored-by-old-reader\n";

        var exception = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.LoadBaseline(Snapshot(
                Source("delta-v0.1", "docs/delta.md", "none"),
                (atom.Path, legacy))));

        Assert.Equal("source delta-v0.1 entry keys are not canonical", exception.Message);
    }

    [Fact]
    public void DirectorySourceProjectsIdentityAndStaleAcknowledgments()
    {
        var source = Source("delta-v0.1", "docs/delta.md", "pzg-v1");
        var atomId = FixtureAtomId("theorem/delta");
        var withStale = source.Text + $"acknowledged_stale = [\"{atomId}\"]\n";
        var inventory = BackfillInventoryLoader.Load(Snapshot(
            (source.Path, withStale),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta")));
        var loadedSource = Assert.Single(inventory.RequireDigestionSources());
        var entry = Assert.Single(loadedSource.Entries);

        Assert.Equal("delta-v0.1", loadedSource.SourceId);
        Assert.Equal("docs/delta.md", loadedSource.SourcePath);
        Assert.Equal("pzg-v1", loadedSource.Atomizer);
        Assert.Equal([atomId], loadedSource.AcknowledgedStale.ToArray());
        Assert.Equal("sha256:" + atomId, entry.Fingerprints.RawSha256);
    }

    [Fact]
    public void DirectoryShapeDerivesTicketsFromAllD5LeanFiles()
    {
        var snapshot = Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"),
            ("D5/X_Frontier/SyntheticDelta.lean", "/-- TASK D5-T0098 -/\ndef frontierTask : Unit := ()\n"),
            ("D5/S1/Depth/Finite.lean", "/-- TASK D5-T0020 -/\ndef depthTask : Unit := ()\n"));

        var tickets = BackfillInventoryLoader.Load(snapshot)
            .RequireTickets()
            .OrderBy(static ticket => ticket.CaseId, StringComparer.Ordinal)
            .Select(static ticket => (ticket.CaseId, ticket.Gid))
            .ToArray();

        Assert.Equal(
            [
                ("D5-T0020", "D5/S1/Depth/Finite"),
                ("D5-T0098", "D5/X_Frontier/SyntheticDelta"),
            ],
            tickets);
    }

    [Fact]
    public void DirectoryShapeRejectsTaskCaseDeclaredByMultipleD5LeanFiles()
    {
        var snapshot = Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"),
            ("D5/S0/Synthetic/First.lean", "/-- TASK D5-T0098 -/\ndef firstTask : Unit := ()\n"),
            ("D5/S1/Synthetic/Second.lean", "/-- TASK D5-T0098 -/\ndef secondTask : Unit := ()\n"));

        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(snapshot));

        Assert.Equal(
            "TASK case D5-T0098 is declared by multiple D5 Lean modules: "
            + "D5/S0/Synthetic/First, D5/S1/Synthetic/Second",
            exception.Message);
    }
}
