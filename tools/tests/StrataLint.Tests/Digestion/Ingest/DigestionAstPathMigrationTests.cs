using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
    [Fact]
    public void IngestMigratesAContentIdenticalAtomWhoseAstPathMoved()
    {
        const string table = "| 条目 | 内容 |\n|---|---|\n| 重复 | 内容 |\n";
        var oldBytes = Encoding.UTF8.GetBytes("## 甲\n\n" + table + "\n## 乙\n\n" + table);
        var newBytes = Encoding.UTF8.GetBytes("## 乙\n\n" + table);
        var oldRows = AtomizerRegistry.Atomize(
            AtomizerRegistry.GenericId,
            oldBytes,
            TheoryAtomizerRules.None).Claims
            .Where(static atom => atom.AstPath.StartsWith("row/重复", StringComparison.Ordinal))
            .ToArray();
        var newAtoms = AtomizerRegistry.Atomize(
            AtomizerRegistry.GenericId,
            newBytes,
            TheoryAtomizerRules.None).Claims;
        var movedAtom = Assert.Single(
            newAtoms,
            static atom => atom.AstPath.StartsWith("row/重复", StringComparison.Ordinal));
        var sectionAtom = Assert.Single(newAtoms, static atom => atom.AstPath == "section/乙");
        Assert.Equal(2, oldRows.Length);
        Assert.True(
            oldRows[0].RawBytes.AsSpan().SequenceEqual(oldRows[1].RawBytes.AsSpan()),
            $"{Convert.ToHexString(oldRows[0].RawBytes.AsSpan())} != "
            + Convert.ToHexString(oldRows[1].RawBytes.AsSpan()));
        Assert.True(
            oldRows[1].RawBytes.AsSpan().SequenceEqual(movedAtom.RawBytes.AsSpan()),
            $"{Convert.ToHexString(oldRows[1].RawBytes.AsSpan())} != "
            + Convert.ToHexString(movedAtom.RawBytes.AsSpan()));
        Assert.NotEqual(oldRows[1].AstPath, movedAtom.AstPath);

        var atomId = "generic-residual-"
            + movedAtom.Fingerprints.RawSha256["sha256:".Length..];
        var receipts = new DigestionReceipts(
            [new DigestionCoverageReceipt(
                "D5/S3/Probe.moved_atom",
                movedAtom.Fingerprints.RawSha256,
                "sha256:" + new string('a', 64))],
            [new DigestionScribeReceipt(
                "D5/S3/Probe.moved_atom",
                "sha256:" + new string('b', 64),
                "sha256:" + new string('c', 64))],
            ["preserve-this-unresolved-subitem"],
            [],
            null);
        var entry = DigestionTestSupport.Entry(
            oldRows[1],
            atomId,
            AtomizerRegistry.GenericId,
            coverageGids: ["D5/S3/Probe.moved_atom"],
            receipts: receipts);
        var sectionEntry = DigestionTestSupport.Entry(
            sectionAtom,
            "existing-section",
            AtomizerRegistry.GenericId);
        var ledger = DigestionTestSupport.Document(
            AtomizerRegistry.GenericId,
            [entry, sectionEntry]);
        var capture = DigestionCasStore.Capture(oldRows[1].RawBytes.AsSpan());
        var sectionCapture = DigestionCasStore.Capture(sectionAtom.RawBytes.AsSpan());

        var plan = DigestionIngestor.Plan(
            ledger,
            DigestionTestSupport.Snapshot(
                ("docs/source.md", newBytes),
                (capture.RelativePath, capture.Bytes.ToArray()),
                (sectionCapture.RelativePath, sectionCapture.Bytes.ToArray())),
            ledger);

        var source = Assert.Single(plan.Document.RequireDigestionSources());
        var migrated = Assert.Single(source.Entries.Where(candidate => candidate.AtomId == atomId));
        Assert.Equal(atomId, migrated.AtomId);
        Assert.Equal(movedAtom.AstPath, migrated.AstPath);
        Assert.Equal(entry.CoverageGids, migrated.CoverageGids);
        Assert.Equal(entry.Receipts, migrated.Receipts);
        Assert.Equal(entry.Receipts.UnresolvedSubitems, migrated.Receipts.UnresolvedSubitems);
        Assert.Equal(entry with { AstPath = movedAtom.AstPath }, migrated);
        Assert.DoesNotContain(atomId, source.AcknowledgedStale);
        Assert.Equal(0, plan.ResidualOpenAdded);
    }

    [Fact]
    public void IngestRejectsAContentIdCollisionWhenTheExistingAstPathIsStillProduced()
    {
        const string table = "| 条目 | 内容 |\n|---|---|\n| 重复 | 内容 |\n";
        var sourceBytes = Encoding.UTF8.GetBytes("## 甲\n\n" + table + "\n## 乙\n\n" + table);
        var atoms = AtomizerRegistry.Atomize(
            AtomizerRegistry.GenericId,
            sourceBytes,
            TheoryAtomizerRules.None).Claims
            .Where(static atom => atom.AstPath.StartsWith("row/重复", StringComparison.Ordinal))
            .ToArray();
        Assert.Equal(2, atoms.Length);
        Assert.True(
            atoms[0].RawBytes.AsSpan().SequenceEqual(atoms[1].RawBytes.AsSpan()),
            $"{Convert.ToHexString(atoms[0].RawBytes.AsSpan())} != "
            + Convert.ToHexString(atoms[1].RawBytes.AsSpan()));
        var atomId = "generic-residual-"
            + atoms[0].Fingerprints.RawSha256["sha256:".Length..];
        var entry = DigestionTestSupport.Entry(
            atoms[0],
            atomId,
            AtomizerRegistry.GenericId);
        var ledger = DigestionTestSupport.Document(
            AtomizerRegistry.GenericId,
            [entry]);
        var capture = DigestionCasStore.Capture(atoms[0].RawBytes.AsSpan());

        var exception = Assert.Throws<FormatException>(() => DigestionIngestor.Plan(
            ledger,
            DigestionTestSupport.Snapshot(
                ("docs/source.md", sourceBytes),
                (capture.RelativePath, capture.Bytes.ToArray())),
            ledger));

        Assert.Equal(
            $"ingest residual atom_id collides with the ledger: {atomId}",
            exception.Message);
    }
}
