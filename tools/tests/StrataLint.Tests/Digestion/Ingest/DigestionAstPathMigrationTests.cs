using System.Collections.Immutable;
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
        const string oldAstPath = "row/original";
        const string movedAstPath = "row/moved";
        var sourceBytes = Encoding.ASCII.GetBytes("same-content\n");
        var atomized = ExplicitAtomization(
            sourceBytes,
            (movedAstPath, 0, sourceBytes.Length));
        var movedAtom = Assert.Single(atomized.Claims);
        var oldAtom = movedAtom with { AstPath = oldAstPath };
        Assert.Equal(oldAstPath, oldAtom.AstPath);
        Assert.Equal(movedAstPath, movedAtom.AstPath);
        Assert.Equal(oldAtom.RawBytes, movedAtom.RawBytes);

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
            oldAtom,
            atomId,
            AtomizerRegistry.GenericId,
            coverageGids: ["D5/S3/Probe.moved_atom"],
            receipts: receipts);
        var ledger = DigestionTestSupport.Document(
            AtomizerRegistry.GenericId,
            [entry]);
        var capture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());

        var plan = DigestionIngestor.Plan(
            ledger,
            DigestionTestSupport.Snapshot(
                ("docs/source.md", sourceBytes),
                (capture.RelativePath, capture.Bytes.ToArray())),
            ledger,
            atomizerResolver: _ => (_, _) => atomized);

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
        const string existingAstPath = "row/existing";
        const string collidingAstPath = "row/colliding";
        var atomBytes = Encoding.ASCII.GetBytes("same-content\n");
        var sourceBytes = atomBytes.Concat(atomBytes).ToArray();
        var atomized = ExplicitAtomization(
            sourceBytes,
            (existingAstPath, 0, atomBytes.Length),
            (collidingAstPath, atomBytes.Length, sourceBytes.Length));
        var atoms = atomized.Claims;
        Assert.Equal(2, atoms.Length);
        Assert.Equal([existingAstPath, collidingAstPath], atoms.Select(static atom => atom.AstPath));
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
            ledger,
            atomizerResolver: _ => (_, _) => atomized));

        Assert.Equal(
            $"ingest residual atom_id collides with the ledger: {atomId}",
            exception.Message);
    }

    private static AtomizedTheoryDocument ExplicitAtomization(
        byte[] sourceBytes,
        params (string AstPath, int StartByte, int EndByte)[] claims)
    {
        var atoms = claims.Select(claim =>
        {
            var rawBytes = sourceBytes[claim.StartByte..claim.EndByte].ToImmutableArray();
            return new DigestionAtom(
                claim.AstPath,
                claim.StartByte,
                claim.EndByte,
                rawBytes,
                DigestionFingerprint.Compute(rawBytes.AsSpan()),
                []);
        }).ToImmutableArray();
        return new AtomizedTheoryDocument(
            atoms,
            atoms.Select(static atom => new DigestionSlice(true, atom.RawBytes)).ToImmutableArray(),
            GenreRegistryCheck.NoGenreRegistry);
    }
}
