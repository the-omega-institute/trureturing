using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RepositoryDigestionTests
{
    [Fact]
    public void RemarkBatchUpgradeCandidatesRemainResidualWithNamedUnresolvedClaims()
    {
        var root = TestRepositoryLayout.FindRoot();
        var entries = BackfillInventoryLoader.LoadRoot(root)
            .RequireDigestionEntries();
        Assert.All(
            entries.Where(static entry => entry.Receipts.Quarantine is not null),
            static entry => Assert.Contains(
                Assert.IsType<string>(entry.Receipts.Quarantine!.BlockerClass),
                DigestionQuarantine.BlockerClasses));
        string[] expectedAtomIds =
        [
            "8eb0bfb6d9c7aa1dc7ddd5faa46452907d7d4aa8efc4b52574393bb91aeed22d",
            "49aad85920afca41580bd9b0a2bac6309cd6930d3f167f277a1f8cdba8835130",
            "163b117bf8d71533380dda3c03c27c13e02d3d02c999a6baebda24fdca60ab45",
            "291ca76328c63069c2958f1a411c23fc9bc197f2d90facb7bd1fff2eb7db34ad",
            "62d1597aaf5576fe27e793a4e7a200b5c32d680149f8f842a37066d686f6b37e",
            "0568a4c0d5dc7153daa2cc47e129eadcb3b5fcc5120fa4940048c651e519aefa",
            "9f92118027a9f11747053931ee56ac8badd298ce7b7171bed1d76d4c80f19322",
            "238bbaa442a0ccdc095f377f556435e13ea9b5923b49ab4a8a135607e047df6c",
            "dc71224083fd410013c0148478a38aede8e0bd4e62827aa1e5a4fcd7eec37333",
        ];

        foreach (var atomId in expectedAtomIds)
        {
            var entry = Assert.Single(entries, entry => entry.AtomId == atomId);

            Assert.Empty(entry.CoverageGids);
            Assert.Empty(entry.Coverage);
            Assert.NotEmpty(entry.Receipts.UnresolvedSubitems);
            Assert.Equal(DigestionMigrationState.Residual, entry.ProjectedStatus.Migration);
            Assert.Equal(DigestionTruthState.Open, entry.ProjectedStatus.Truth);
        }
    }
}
