using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
    [Fact]
    public void IngestAcknowledgesCoveredPriorGenerationStaleWhenReatomizedTextSupersedesIt()
    {
        const string gid =
            "D5/S3/Observer/WindowCharacter.window_algebra_has_no_character";
        var oldBytes = Encoding.UTF8.GetBytes(
            "# SYNTH-VOL\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# SYNTH-VOL\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(
            AtomizerRegistry.GictId,
            oldBytes,
            DigestionTestSupport.Rules).Claims);
        var currentAtom = Assert.Single(AtomizerRegistry.Atomize(
            AtomizerRegistry.GictId,
            currentBytes,
            DigestionTestSupport.Rules).Claims);
        var oldAtomId = "gict-residual-"
            + oldAtom.Fingerprints.RawSha256["sha256:".Length..];
        var currentAtomId = "gict-residual-"
            + currentAtom.Fingerprints.RawSha256["sha256:".Length..];
        Assert.Equal(oldAtom.AstPath, currentAtom.AstPath);
        Assert.NotEqual(oldAtomId, currentAtomId);

        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var oldEntry = DigestionTestSupport.Entry(
            oldAtom,
            oldAtomId,
            AtomizerRegistry.GictId,
            migration: DigestionMigrationState.Absorbed,
            truth: DigestionTruthState.Closed,
            coverageGids: [gid],
            receipts: new DigestionReceipts(
                [new DigestionCoverageReceipt(
                    gid,
                    oldAtom.Fingerprints.RawSha256,
                    "sha256:" + new string('a', 64))],
                [new DigestionScribeReceipt(
                    gid,
                    "sha256:" + new string('b', 64),
                    "sha256:" + new string('c', 64))],
                [],
                [],
                null),
            casRef: oldCapture.Reference);
        var ledger = DigestionTestSupport.Document(
            AtomizerRegistry.GictId,
            [oldEntry]);
        var oldFormalizationReceipt = DigestionFormalizationReceipt.Write(
            new DigestionFormalizationReceipt(
                oldAtomId,
                gid,
                new DigestionFormalizationSignature(
                    "window_algebra_has_no_character",
                    "theorem",
                    "True"),
                oldAtom.Fingerprints.RawSha256,
                oldAtom.Fingerprints.RawSha256));
        var oldFormalizationPath = DigestionFormalizationReceipt.PathForAtom(oldAtomId);
        var snapshot = DigestionTestSupport.Snapshot(
            ("docs/source.md", currentBytes),
            (oldCapture.RelativePath, oldCapture.Bytes.ToArray()),
            (oldFormalizationPath, oldFormalizationReceipt.ToArray()));

        var plan = DigestionIngestor.Plan(ledger, snapshot, ledger, snapshot);

        var source = Assert.Single(plan.Document.RequireDigestionSources());
        var retainedOldEntry = Assert.Single(
            source.Entries,
            entry => entry.AtomId == oldAtomId);
        var newEntry = Assert.Single(
            source.Entries,
            entry => entry.AtomId == currentAtomId);
        Assert.Equal(oldEntry, retainedOldEntry);
        Assert.Contains(oldAtomId, source.AcknowledgedStale);
        Assert.Empty(newEntry.CoverageGids);
        Assert.Equal(
            new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open),
            newEntry.ProjectedStatus);

        var sourceMetadata = BackfillInventoryWriter.WriteSourceMetadata(
            Assert.Single(ledger.RequireDigestionSources()));
        var currentRaw = RawRepositorySnapshot.Create(snapshot.Files.Values
            .Select(static file => new RawRepositoryEntry(file.Path.Value, file.RawBytes))
            .Append(new RawRepositoryEntry(
                $"{BackfillInventoryLoader.RootPath}source/source.toml",
                sourceMetadata))
            .Append(new RawRepositoryEntry(
                $"{BackfillInventoryLoader.RootPath}source/absorbed-closed/{oldAtomId}.yaml",
                BackfillInventoryWriter.WriteAtom(oldEntry))));
        var replaced = IngestCommand.ReplaceLedger(currentRaw, ledger, plan.Document);
        Assert.Equal(
            oldFormalizationReceipt.ToArray(),
            Assert.Single(replaced.Entries, entry => entry.Path == oldFormalizationPath)
                .Bytes
                .ToArray());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void IngestInheritsCoverageAcrossAtomGenerationsOnlyWhenNewPairIsReceipted(
        bool hasNewGenerationReceipt)
    {
        const string gid =
            "D5/S3/Observer/WindowCharacter.window_algebra_has_no_character";
        const string unresolvedSubitem = "preserve-this-unresolved-subitem";
        var oldBytes = Encoding.UTF8.GetBytes(
            "# SYNTH-VOL\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# SYNTH-VOL\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(
            AtomizerRegistry.GictId,
            oldBytes,
            DigestionTestSupport.Rules).Claims);
        var currentAtom = Assert.Single(AtomizerRegistry.Atomize(
            AtomizerRegistry.GictId,
            currentBytes,
            DigestionTestSupport.Rules).Claims);
        var oldAtomId = "gict-residual-"
            + oldAtom.Fingerprints.RawSha256["sha256:".Length..];
        var currentAtomId = "gict-residual-"
            + currentAtom.Fingerprints.RawSha256["sha256:".Length..];
        Assert.Equal(oldAtom.AstPath, currentAtom.AstPath);
        Assert.NotEqual(oldAtomId, currentAtomId);

        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var oldEntry = DigestionTestSupport.Entry(
            oldAtom,
            oldAtomId,
            AtomizerRegistry.GictId,
            coverageGids: [gid],
            receipts: new DigestionReceipts(
                [new DigestionCoverageReceipt(
                    gid,
                    oldAtom.Fingerprints.RawSha256,
                    "sha256:" + new string('a', 64))],
                [],
                [unresolvedSubitem],
                [],
                null),
            casRef: oldCapture.Reference);
        var ledger = DigestionTestSupport.Document(
            AtomizerRegistry.GictId,
            [oldEntry],
            acknowledgedStale: [oldAtomId]);
        var snapshotFiles = new List<(string Path, byte[] Bytes)>
        {
            ("docs/source.md", currentBytes),
            (oldCapture.RelativePath, oldCapture.Bytes.ToArray()),
        };
        if (hasNewGenerationReceipt)
        {
            var receipt = new DigestionFormalizationReceipt(
                currentAtomId,
                gid,
                new DigestionFormalizationSignature(
                    "window_algebra_has_no_character",
                    "theorem",
                    "True"),
                currentAtom.Fingerprints.RawSha256,
                currentAtom.Fingerprints.RawSha256);
            snapshotFiles.Add((
                DigestionFormalizationReceipt.PathForAtom(currentAtomId),
                DigestionFormalizationReceipt.Write(receipt).ToArray()));
        }

        var snapshot = DigestionTestSupport.Snapshot(snapshotFiles.ToArray());
        var plan = DigestionIngestor.Plan(ledger, snapshot, ledger, snapshot);

        var source = Assert.Single(plan.Document.RequireDigestionSources());
        var newEntry = Assert.Single(
            source.Entries,
            entry => entry.AtomId == currentAtomId);
        Assert.Contains(oldEntry, source.Entries);
        Assert.Equal(
            hasNewGenerationReceipt ? [gid] : Array.Empty<string>(),
            newEntry.CoverageGids.ToArray());
        Assert.Empty(newEntry.Receipts.Coverage);
        if (hasNewGenerationReceipt)
        {
            return;
        }

        Assert.Contains(oldAtomId, source.AcknowledgedStale);
        Assert.Equal([unresolvedSubitem], newEntry.Receipts.UnresolvedSubitems.ToArray());
        Assert.Equal(
            new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open),
            newEntry.ProjectedStatus);
    }

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
