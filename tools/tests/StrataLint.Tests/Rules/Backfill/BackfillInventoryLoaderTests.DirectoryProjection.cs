using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class BackfillInventoryLoaderTests
{
    [Fact]
    public void DirectoryLedgerProjectsCoverageReferences()
    {
        var atom = Atom("delta-v0.1", "partial-open", "delta-atom", "manual/delta");
        var withCoverage = atom.Text.Replace(
            "coverage_gids: []",
            "coverage_gids:\n  - D5/X_Frontier/SyntheticSourceTarget",
            StringComparison.Ordinal);
        var inventory = BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, withCoverage)));

        Assert.Equal(
            ["D5/X_Frontier/SyntheticSourceTarget"],
            inventory.RequireReferencedGids().ToArray());
    }

    [Fact]
    public void DirectorySourceProjectsIdentityAndStaleAcknowledgments()
    {
        var source = Source("delta-v0.1", "docs/delta.md", "pzg-v1");
        var withStale = source.Text + "acknowledged_stale = [\"delta-atom\"]\n";
        var inventory = BackfillInventoryLoader.Load(Snapshot(
            (source.Path, withStale),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta")));
        var loadedSource = Assert.Single(inventory.RequireDigestionSources());
        var entry = Assert.Single(loadedSource.Entries);

        Assert.Equal("delta-v0.1", loadedSource.SourceId);
        Assert.Equal("docs/delta.md", loadedSource.SourcePath);
        Assert.Equal("pzg-v1", loadedSource.Atomizer);
        Assert.Equal(["delta-atom"], loadedSource.AcknowledgedStale.ToArray());
        Assert.Equal("theorem/delta", entry.AstPath);
        Assert.Null(entry.Boundary);
    }

    [Theory]
    [InlineData("[]")]
    [InlineData("null")]
    [InlineData("~")]
    [InlineData("0")]
    [InlineData("+1")]
    [InlineData("01")]
    public void DirectoryAtomWriterQuotesYamlScalarLookingAstPaths(string astPath)
    {
        var atom = Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta");
        var entry = Assert.Single(BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            atom)).RequireDigestionEntries()) with
        {
            AstPath = astPath,
        };

        var written = Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(entry).AsSpan());
        var roundTripped = BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, written)));

        Assert.Equal(astPath, Assert.Single(roundTripped.RequireDigestionEntries()).AstPath);
        Assert.Contains($"ast_path: '{astPath}'", written, StringComparison.Ordinal);
    }

    [Fact]
    public void RemarkBatchUpgradeCandidatesRemainResidualWithNamedUnresolvedClaims()
    {
        var root = TestRepositoryLayout.FindRoot();
        var entries = BackfillInventoryLoader.LoadRoot(root)
            .RequireDigestionEntries();
        string[] expectedPaths =
        [
            "remark/6.37",
            "remark/6.43",
            "remark/10.11",
            "remark/27.20",
            "remark/27.25",
            "remark/27.30",
            "remark/27.35",
            "remark/27.41",
            "remark/27.95",
        ];

        foreach (var path in expectedPaths)
        {
            var entry = Assert.Single(entries, entry => entry.AstPath == path);

            Assert.Empty(entry.CoverageGids);
            Assert.Empty(entry.Receipts.Coverage);
            Assert.Empty(entry.Receipts.Scribe);
            Assert.NotEmpty(entry.Receipts.UnresolvedSubitems);
            Assert.Equal(DigestionMigrationState.Residual, entry.ProjectedStatus.Migration);
            Assert.Equal(DigestionTruthState.Open, entry.ProjectedStatus.Truth);
        }
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
