using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void IngestReplacementRejectsLegacySingleFileLedger()
    {
        var ledger = IngestLedger(
            SyntheticNumberedAtomizer.Id,
            Assert.Single(AtomizerRegistry.Atomize(
                SyntheticNumberedAtomizer.Id,
                Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。claim。\n"),
                DigestionTestSupport.Rules).Claims));
        var raw = RawRepositorySnapshot.Create([
            new RawRepositoryEntry(
                BackfillInventoryLoader.RelativePath,
                [.. Encoding.UTF8.GetBytes(DirectoryLedgerTestSupport.Image(ledger))]),
        ]);

        var exception = Assert.Throws<InvalidOperationException>(() => IngestCommand.ReplaceLedger(
            raw,
            ledger,
            ledger));

        Assert.Equal("ingest does not write legacy digestion ledgers", exception.Message);
    }

    [Fact]
    public void AtomicLedgerReplacementPreservesExistingBytesWhenCommitFails()
    {
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        var original = Encoding.UTF8.GetBytes("original ledger\n");
        var replacement = Encoding.UTF8.GetBytes("replacement ledger\n");
        File.WriteAllBytes(outputPath, original);
        string? pendingPath = null;

        var exception = Assert.Throws<IOException>(() => IngestCommand.ReplaceLedgerAtomically(
            outputPath,
            replacement,
            (pending, target) =>
            {
                pendingPath = pending;
                Assert.Equal(Path.GetDirectoryName(target), Path.GetDirectoryName(pending));
                Assert.Equal(original, File.ReadAllBytes(target));
                Assert.Equal(replacement, File.ReadAllBytes(pending));
                throw new IOException("simulated atomic commit failure");
            }));

        Assert.Equal("simulated atomic commit failure", exception.Message);
        Assert.Equal(original, File.ReadAllBytes(outputPath));
        Assert.NotNull(pendingPath);
        Assert.False(File.Exists(pendingPath));
    }

    [Fact]
    public void DirectoryLedgerUpdateRollsBackEarlierFilesWhenALaterCommitFails()
    {
        using var temporary = new TemporaryDirectory();
        var firstPath = $"{BackfillInventoryLoader.RootPath}fixture-source/residual-open/first.yaml";
        var secondPath = $"{BackfillInventoryLoader.RootPath}fixture-source/residual-open/second.yaml";
        var firstBytes = Encoding.UTF8.GetBytes("first original\n");
        var secondBytes = Encoding.UTF8.GetBytes("second original\n");
        var current = RawRepositorySnapshot.Create([
            new RawRepositoryEntry(firstPath, [.. firstBytes]),
            new RawRepositoryEntry(secondPath, [.. secondBytes]),
        ]);
        foreach (var entry in current.Entries)
        {
            var outputPath = Path.Combine(
                temporary.Path,
                entry.Path.Replace('/', Path.DirectorySeparatorChar));
            Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
            File.WriteAllBytes(outputPath, entry.Bytes.AsSpan());
        }

        var commits = 0;
        var exception = Assert.Throws<IOException>(() => IngestCommand.ApplyLedgerUpdatesAtomically(
            temporary.Path,
            current,
            [
                new IngestCommand.LedgerUpdate(firstPath, [.. Encoding.UTF8.GetBytes("first replacement\n")]),
                new IngestCommand.LedgerUpdate(secondPath, [.. Encoding.UTF8.GetBytes("second replacement\n")]),
            ],
            (pending, target) =>
            {
                commits++;
                if (commits == 2)
                {
                    throw new IOException("simulated second ledger commit failure");
                }

                File.Move(pending, target, overwrite: true);
            }));

        Assert.Equal("simulated second ledger commit failure", exception.Message);
        Assert.Equal(firstBytes, File.ReadAllBytes(Path.Combine(
            temporary.Path,
            firstPath.Replace('/', Path.DirectorySeparatorChar))));
        Assert.Equal(secondBytes, File.ReadAllBytes(Path.Combine(
            temporary.Path,
            secondPath.Replace('/', Path.DirectorySeparatorChar))));
    }

    [Fact]
    public void DirectoryLedgerDeletionPrunesDirectoriesAfterAllRankedFilesAreGone()
    {
        using var temporary = new TemporaryDirectory();
        var sourcePath = $"{BackfillInventoryLoader.RootPath}fixture-source/source.toml";
        var parentPath = $"{BackfillInventoryLoader.RootPath}fixture-source/residual-open/parent.yaml";
        var childPath = $"{BackfillInventoryLoader.RootPath}fixture-source/residual-open/child.yaml";
        var current = RawRepositorySnapshot.Create(
        [
            RawRepositoryEntry.FromText(sourcePath, "source metadata\n"),
            RawRepositoryEntry.FromText(parentPath, "parent\n"),
            RawRepositoryEntry.FromText(childPath, "child\n"),
        ]);
        foreach (var entry in current.Entries)
        {
            var outputPath = Path.Combine(
                temporary.Path,
                entry.Path.Replace('/', Path.DirectorySeparatorChar));
            Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
            File.WriteAllBytes(outputPath, entry.Bytes.AsSpan());
        }

        IngestCommand.ApplyLedgerUpdatesAtomically(
            temporary.Path,
            current,
            [
                new IngestCommand.LedgerUpdate(parentPath, null, int.MaxValue - 1),
                new IngestCommand.LedgerUpdate(childPath, null, int.MaxValue),
                new IngestCommand.LedgerUpdate(sourcePath, null, int.MaxValue),
            ]);

        var ledgerRoot = Path.Combine(
            temporary.Path,
            BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar));
        Assert.True(Directory.Exists(ledgerRoot));
        Assert.False(Directory.Exists(Path.Combine(ledgerRoot, "fixture-source", "residual-open")));
        Assert.False(Directory.Exists(Path.Combine(ledgerRoot, "fixture-source")));
    }

    [Fact]
    public void DirectoryLedgerWritePlanNeverPublishesParentBeforeItsChildren()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 18.7(写序)**。first clause。\n\n"
            + "**推论:第二子句**;the full plan has two clauses。\n");
        var atomized = PzgAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules);
        var parentAtom = Assert.Single(atomized.Claims);
        var children = Assert.Single(atomized.ClausePlans).Children;
        var currentDocument = MapOnlyEntry(
            IngestLedger(AtomizerRegistry.PzgId, parentAtom),
            entry => entry with { AtomId = "parent" });
        var source = Assert.Single(currentDocument.RequireDigestionSources());
        var parent = Assert.Single(source.Entries);
        var childIds = new[] { "pzg-child-1", "pzg-child-2" };
        DigestionLedgerEntry ChildEntry(int index) => parent with
        {
            AtomId = childIds[index],
            Fingerprints = children[index].Fingerprints,
            CasRef = children[index].Fingerprints.RawSha256,
            Receipts = new DigestionReceipts([], [], [], [], null),
        };
        var finalDocument = currentDocument.WithDigestionSources(
        [
            source with
            {
                Entries =
                [
                    parent with
                    {
                        Receipts = parent.Receipts with { ChainAtoms = [.. childIds] },
                    },
                    ChildEntry(0),
                    ChildEntry(1),
                ],
            },
        ]);
        var currentFiles = new Dictionary<string, string>(StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(currentFiles, currentDocument);
        var currentRaw = RawRepositorySnapshot.Create(currentFiles.Select(static pair =>
            RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var finalRaw = IngestCommand.ReplaceLedger(
            currentRaw,
            currentDocument,
            finalDocument);
        var updates = IngestCommand.LedgerUpdates(currentRaw, finalRaw);
        var prefix = currentRaw.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);

        Assert.Equal(3, updates.Length);
        foreach (var update in updates)
        {
            if (update.Bytes is { } bytes)
            {
                prefix[update.Path] = new RawRepositoryEntry(update.Path, bytes);
            }
            else
            {
                prefix.Remove(update.Path);
            }

            var rawPrefix = RawRepositorySnapshot.Create(prefix.Values);
            var decoded = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
                SnapshotDecoder.Decode(rawPrefix)).Snapshot;
            var prefixDocument = BackfillInventoryLoader.Load(decoded);
            var present = prefixDocument.RequireDigestionEntries()
                .Select(static entry => entry.AtomId)
                .ToHashSet(StringComparer.Ordinal);
            Assert.All(prefixDocument.RequireDigestionEntries(), entry => Assert.All(
                entry.Receipts.ChainAtoms,
                childId => Assert.Contains(childId, present)));
        }
    }

    [Theory]
    [InlineData("coverage-receipt-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void IngestRejectsEachNewReceiptIntegrityMismatchBeforeWritingLedger(string mismatchCode)
    {
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            OtherAtomGid = "D5/S0/Carrier/Probe.probe",
        });
        var inputs = DirectoryInputs(WithSiblingReceiptMismatch(materialized, mismatchCode));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var environment = BuildCoverEnvironment(
            temporary.Path,
            inputs,
            inputs.Files,
            RawChangeSet.Create(["D5/S0/Carrier/Probe.lean"]));

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("digest status is invalid", result.Error, StringComparison.Ordinal);
        Assert.Contains(mismatchCode, result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    [Fact]
    public void IngestAtomizesNewSourceWhileUnrelatedReceiptIntegrityBacklogExistsAtForkPoint()
    {
        const string newSourcePath = "docs/develop/theory/INGEST_SCOPE_NEW_SOURCE.md";
        const string newSourceText = "# New source\n\n## Theorem 1.1\n\nClaim.\n";
        const string siblingModuleGid = "D5/S0/Carrier/CoverSibling";
        const string siblingGid = siblingModuleGid + ".sibling";
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            SecondaryTarget = (siblingModuleGid, "sibling"),
            UnrelatedSibling = new CoverUnrelatedSiblingSpec(
                [siblingGid],
                [siblingGid],
                []),
        });
        var inputs = DirectoryInputs(WithSiblingReceiptMismatch(
            materialized,
            "coverage-receipt-mismatch"));
        var files = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal)
        {
            [newSourcePath] = newSourceText,
        };
        inputs = inputs with { Files = files };
        var backlogAtom = Assert.Single(inputs.Files, pair => pair.Key.EndsWith(
            "/" + CoverWorld.UnrelatedAtomId + ".yaml",
            StringComparison.Ordinal));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var environment = BuildCoverEnvironment(
            temporary.Path,
            inputs,
            inputs.Files,
            RawChangeSet.Create([newSourcePath]));

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain(
            CoverWorld.UnrelatedAtomId + ":coverage-receipt-mismatch",
            result.Output,
            StringComparison.Ordinal);
        var written = BackfillInventoryLoader.LoadRoot(temporary.Path);
        var newSource = Assert.Single(
            written.RequireDigestionSources(),
            static source => source.SourceId == "ingest-scope-new-source");
        Assert.Single(newSource.Entries);
        Assert.Contains(
            backlogAtom.Key
            + "\0"
            + Convert.ToBase64String(Encoding.UTF8.GetBytes(backlogAtom.Value))
            + "\n",
            DirectoryLedgerTestSupport.Image(temporary.Path),
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestRejectsTouchedReceiptIntegrityGapWhoseForkPointIdentityIsUnchanged()
    {
        const string siblingModuleGid = "D5/S0/Carrier/CoverSibling";
        const string siblingGid = siblingModuleGid + ".sibling";
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            SecondaryTarget = (siblingModuleGid, "sibling"),
            UnrelatedSibling = new CoverUnrelatedSiblingSpec(
                [siblingGid],
                [siblingGid],
                []),
        });
        var inputs = DirectoryInputs(WithSiblingReceiptMismatch(
            materialized,
            "coverage-receipt-mismatch"));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var environment = BuildCoverEnvironment(
            temporary.Path,
            inputs,
            inputs.Files,
            RawChangeSet.Create([siblingModuleGid + ".lean"]));

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains(
            $"{CoverWorld.UnrelatedAtomId}:coverage-receipt-mismatch:{siblingGid}",
            result.Error,
            StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

}
