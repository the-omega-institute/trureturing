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
        string[] fixturePaths =
        [
            "Meta/Digestion/backfill/pzg-v170/source.toml",
            "Meta/Digestion/backfill/pzg-v170/residual-open/pzg-residual-0568a4c0d5dc7153daa2cc47e129eadcb3b5fcc5120fa4940048c651e519aefa.yaml",
            "Meta/Digestion/backfill/pzg-v170/residual-open/pzg-residual-163b117bf8d71533380dda3c03c27c13e02d3d02c999a6baebda24fdca60ab45.yaml",
            "Meta/Digestion/backfill/pzg-v170/residual-open/pzg-residual-238bbaa442a0ccdc095f377f556435e13ea9b5923b49ab4a8a135607e047df6c.yaml",
            "Meta/Digestion/backfill/pzg-v170/residual-open/pzg-residual-291ca76328c63069c2958f1a411c23fc9bc197f2d90facb7bd1fff2eb7db34ad.yaml",
            "Meta/Digestion/backfill/pzg-v170/residual-open/pzg-residual-49aad85920afca41580bd9b0a2bac6309cd6930d3f167f277a1f8cdba8835130.yaml",
            "Meta/Digestion/backfill/pzg-v170/residual-open/pzg-residual-62d1597aaf5576fe27e793a4e7a200b5c32d680149f8f842a37066d686f6b37e.yaml",
            "Meta/Digestion/backfill/pzg-v170/residual-open/pzg-residual-8eb0bfb6d9c7aa1dc7ddd5faa46452907d7d4aa8efc4b52574393bb91aeed22d.yaml",
            "Meta/Digestion/backfill/pzg-v170/residual-open/pzg-residual-9f92118027a9f11747053931ee56ac8badd298ce7b7171bed1d76d4c80f19322.yaml",
            "Meta/Digestion/backfill/pzg-v170/residual-open/pzg-residual-dc71224083fd410013c0148478a38aede8e0bd4e62827aa1e5a4fcd7eec37333.yaml",
        ];
        var entries = BackfillInventoryLoader.Load(Snapshot(fixturePaths.Select(path =>
                (path, TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(path))))
            .ToArray()))
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
