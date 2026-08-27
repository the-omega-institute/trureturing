using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class BackfillInventoryLoaderTests
{
    [Fact]
    public void CoverageReceiptRejectsLegacyTargetSha256Field()
    {
        var atom = Atom("delta-v0.1", "partial-closed", "delta-atom", "theorem/delta");
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, LegacyCoverageAtom(atom.Text)))));

        Assert.Contains("coverage receipt keys are not canonical", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void BaselineCoverageReceiptPreservesLegacyTargetWithoutStatementBinding()
    {
        const string legacyTarget =
            "sha256:2222222222222222222222222222222222222222222222222222222222222222";
        var atom = Atom("delta-v0.1", "partial-closed", "delta-atom", "theorem/delta");
        var entry = Assert.Single(BackfillInventoryLoader.LoadBaseline(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, LegacyCoverageAtom(atom.Text)))).RequireDigestionEntries());
        var receipt = Assert.Single(entry.Receipts.Coverage);

        Assert.Null(receipt.TargetStatementId);
        Assert.Equal(legacyTarget, receipt.LegacyTargetSha256);
        var exception = Assert.Throws<InvalidOperationException>(() =>
            BackfillInventoryWriter.WriteAtom(entry));
        Assert.Equal(
            "legacy coverage receipt for D5/S0/Carrier/Probe.target cannot be written as a statement-bound receipt",
            exception.Message);
    }

    [Fact]
    public void CandidateDeltaTrustsUnchangedLegacyCoverageReceipt()
    {
        var source = Source("delta-v0.1", "docs/delta.md", "none");
        var atom = Atom("delta-v0.1", "partial-closed", "delta-atom", "theorem/delta");
        var legacy = LegacyCoverageAtom(atom.Text);
        var baseline = Snapshot(source, (atom.Path, legacy));
        var candidate = Snapshot(source, (atom.Path, legacy));

        var document = BackfillInventoryLoader.LoadCandidateDelta(
            candidate,
            baseline,
            RawChangeSet.Create(["D5/S3/Probe/Unrelated.lean"]));

        var receipt = Assert.Single(Assert.Single(
            document.RequireDigestionEntries()).Receipts.Coverage);
        Assert.Null(receipt.TargetStatementId);
        Assert.Equal(
            "sha256:2222222222222222222222222222222222222222222222222222222222222222",
            receipt.LegacyTargetSha256);
    }

    [Fact]
    public void CandidateDeltaRejectsChangedLegacyCoverageReceipt()
    {
        var source = Source("delta-v0.1", "docs/delta.md", "none");
        var atom = Atom("delta-v0.1", "partial-closed", "delta-atom", "theorem/delta");
        var baseline = Snapshot(source, atom);
        var candidate = Snapshot(source, (atom.Path, LegacyCoverageAtom(atom.Text)));

        var exception = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.LoadCandidateDelta(
                candidate,
                baseline,
                RawChangeSet.Create([atom.Path])));

        Assert.Contains("coverage receipt keys are not canonical", exception.Message, StringComparison.Ordinal);
    }

    private static string LegacyCoverageAtom(string atom) => atom
        .Replace(
            "coverage_gids: []",
            "coverage_gids:\n  - D5/S0/Carrier/Probe.target",
            StringComparison.Ordinal)
        .Replace(
            "  coverage: []",
            "  coverage:\n"
            + "    - gid: D5/S0/Carrier/Probe.target\n"
            + "      source_sha256: sha256:1111111111111111111111111111111111111111111111111111111111111111\n"
            + "      target_sha256: sha256:2222222222222222222222222222222222222222222222222222222222222222",
            StringComparison.Ordinal);
}
