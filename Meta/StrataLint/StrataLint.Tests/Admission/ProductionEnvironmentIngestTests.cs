using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void IngestReadsTheDirectoryFormDigestionLedger()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。claim。\n");
        var atom = Assert.Single(AtomizerRegistry.Atomize(
            atomizerId,
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        InstallDirectoryLedger(fixture, atomizerId, atom);
        using var temporary = new TemporaryDirectory();
        var atomPath = DirectoryAtomPath("old-receipt", "residual-open");
        var outputPath = Path.Combine(
            temporary.Path,
            atomPath.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, DirectoryAtom(atom), new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.Ingest(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("ledger_changed=false", result.Output, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(
            temporary.Path,
            BackfillInventoryLoader.RelativePath.Replace('/', Path.DirectorySeparatorChar))));
    }

    [Fact]
    public void IngestMovesDirectoryAtomWhenDerivedStatusChangesFromResidualToPartial()
    {
        const string coverageGid = "D5/S0/Carrier/Ring";
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。claim。\n");
        var atom = Assert.Single(AtomizerRegistry.Atomize(
            atomizerId,
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        InstallDirectoryLedger(fixture, atomizerId, atom);
        var oldPath = DirectoryAtomPath("old-receipt", "residual-open");
        var atomText = DirectoryAtom(atom).Replace(
            "coverage_gids: []",
            $"coverage_gids:\n  - {coverageGid}",
            StringComparison.Ordinal);
        fixture.Files[oldPath] = atomText;
        fixture.Baseline[oldPath] = atomText;
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.Ingest(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        var newPath = DirectoryAtomPath("old-receipt", "partial-closed");
        Assert.False(File.Exists(Path.Combine(
            temporary.Path,
            oldPath.Replace('/', Path.DirectorySeparatorChar))));
        var outputPath = Path.Combine(
            temporary.Path,
            newPath.Replace('/', Path.DirectorySeparatorChar));
        Assert.True(File.Exists(outputPath));
        var entry = Assert.Single(BackfillInventoryLoader.LoadRoot(temporary.Path)
            .RequireDigestionEntries());
        Assert.Equal(DigestionMigrationState.Partial, entry.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, entry.ProjectedStatus.Truth);
        Assert.Equal([coverageGid], entry.CoverageGids.ToArray());
        Assert.Equal(BackfillInventoryWriter.WriteAtom(entry).ToArray(), File.ReadAllBytes(outputPath));
    }

    [Fact]
    public void IngestFansOutDirectoryLedgerUpdatesWithoutTouchingUnchangedAtoms()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。rewritten。\n\n**定理 1.2(B)**。new。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(
            atomizerId,
            oldBytes,
            DigestionTestSupport.Rules).Claims);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        InstallDirectoryLedger(fixture, atomizerId, oldAtom);
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var existingPath = Path.Combine(
            temporary.Path,
            DirectoryAtomPath("old-receipt", "residual-open")
                .Replace('/', Path.DirectorySeparatorChar));
        var unchangedWriteTime = new DateTime(2000, 1, 1, 0, 0, 0, DateTimeKind.Utc);
        File.SetLastWriteTimeUtc(existingPath, unchangedWriteTime);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.Ingest(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("residual_open_added=2", result.Output, StringComparison.Ordinal);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.Equal(unchangedWriteTime, File.GetLastWriteTimeUtc(existingPath));
        Assert.False(File.Exists(Path.Combine(
            temporary.Path,
            BackfillInventoryLoader.RelativePath.Replace('/', Path.DirectorySeparatorChar))));
        var written = BackfillInventoryLoader.LoadRoot(temporary.Path);
        Assert.Equal(3, written.RequireDigestionEntries().Length);
        var atomFiles = Directory.GetFiles(
            Path.Combine(temporary.Path, BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar)),
            "*.yaml",
            SearchOption.AllDirectories);
        Assert.Equal(3, atomFiles.Length);
        Assert.All(atomFiles, path => Assert.Equal(
            "residual-open",
            Directory.GetParent(path)!.Name));
    }

    [Fact]
    public void DirectoryLedgerReplacementWritesChangedSourceMetadataOnly()
    {
        var files = DirectoryLedgerTestSupport.Project(new RuleFixture().Files);
        var raw = RawRepositorySnapshot.Create(files.Select(static pair =>
            RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var decoded = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var current = BackfillInventoryLoader.Load(decoded);
        var source = Assert.Single(current.RequireDigestionSources());
        var replacement = current.WithDigestionSources([
            source with { AcknowledgedStale = [source.Entries[0].AtomId] },
        ]);
        var unchangedAtom = raw.Entries.Single(entry => entry.Path.EndsWith(
            $"/{source.Entries[0].AtomId}.yaml",
            StringComparison.Ordinal));

        var replaced = IngestCommand.ReplaceLedger(
            raw,
            current,
            replacement,
            BackfillInventoryWriter.WriteForIngest(replacement));
        var redecoded = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(replaced)).Snapshot;
        var written = BackfillInventoryLoader.Load(redecoded);

        Assert.Equal(
            [source.Entries[0].AtomId],
            Assert.Single(written.RequireDigestionSources()).AcknowledgedStale.ToArray());
        Assert.Equal(
            unchangedAtom.Bytes.ToArray(),
            replaced.Entries.Single(entry => entry.Path == unchangedAtom.Path).Bytes.ToArray());
    }

    [Fact]
    public void IngestWritesOneCommitReadyLedgerUpdateAndRecomputesDigestStatus()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。rewritten。\n\n**定理 1.2(B)**。new。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes, DigestionTestSupport.Rules).Claims);
        var ledger = IngestLedger(atomizerId, oldAtom)
            .Replace("atom_id: old-receipt", "atom_id: '123'", StringComparison.Ordinal)
            .Replace("migration: residual", "migration: absorbed", StringComparison.Ordinal);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        InstallLedger(fixture, ledger, oldAtom);
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, ledger, new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.Ingest(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("stale_acknowledged=0", result.Output, StringComparison.Ordinal);
        Assert.Contains("residual_open_added=2", result.Output, StringComparison.Ordinal);
        Assert.Contains("cas_objects_written=2", result.Output, StringComparison.Ordinal);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.Contains("DIGEST_STATUS entries=3", result.Output, StringComparison.Ordinal);
        var writtenText = File.ReadAllText(outputPath);
        var written = BackfillInventoryLoader.Load(writtenText);
        var source = Assert.Single(written.RequireDigestionSources());
        Assert.Empty(source.AcknowledgedStale);
        Assert.Equal(3, source.Entries.Length);
        Assert.Equal(
            DigestionMigrationState.Residual,
            source.Entries.Single(static entry => entry.AtomId == "123").ProjectedStatus.Migration);
        var casBacked = source.Entries.Where(static entry => entry.AtomId != "123").ToArray();
        Assert.Equal(2, casBacked.Length);
        foreach (var entry in casBacked)
        {
            var relativePath = DigestionCasStore.RootPath
                + entry.CasRef["sha256:".Length..];
            var bytes = File.ReadAllBytes(Path.Combine(
                temporary.Path,
                relativePath.Replace('/', Path.DirectorySeparatorChar)));
            Assert.Equal(entry.CasRef, DigestionCasStore.Capture(bytes).Reference);
        }

        Assert.Contains("atom_id: '123'", writtenText, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestRejectsStructurallyInvalidLedgerWithoutWriting()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。claim。\n");
        var atom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, sourceBytes, DigestionTestSupport.Rules).Claims);
        var ledger = IngestLedger(atomizerId, atom).Replace(
            "source_id: fixture-source",
            "source_id: INVALID",
            StringComparison.Ordinal);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        InstallLedger(fixture, ledger, atom);
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, ledger, new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.Ingest(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("invalid source_id: INVALID", result.Error, StringComparison.Ordinal);
        Assert.Equal(ledger, File.ReadAllText(outputPath));
    }

    [Fact]
    public void IngestPerformsFirstExtractionForRegisteredEmptySource()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceText = "# Synthetic\n\n**定理 1.1(A)**。claim。\n";
        var ledger = $$"""
            schema_version: 3
            ledger: theory-digestion-v1
            sources:
              - source_id: fixture-source
                path: {{GoldenCorpus.FixtureDigestionSourcePath}}
                atomizer: {{atomizerId}}
                entries: []
            ticket_index: []
            """;
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = sourceText;
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = sourceText;
        InstallLedger(fixture, ledger, existingAtom: null);
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, ledger, new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.Ingest(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        var written = File.ReadAllText(outputPath);
        Assert.NotEqual(ledger, written);
        Assert.Contains("atom_id:", written, StringComparison.Ordinal);
        Assert.True(Directory.Exists(Path.Combine(temporary.Path, "Meta", "Digestion")));
    }

    [Fact]
    public void IngestWarnsWhenChangedTheorySourceProducesNoNewAtoms()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldText = "# Synthetic\n\n**定理 1.1(A)**。claim。\n\n## Existing\n\nold prose。\n";
        var currentText = oldText + "\n## Added dialect\n\nnew unrecognized prose。\n";
        var oldBytes = Encoding.UTF8.GetBytes(oldText);
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes, DigestionTestSupport.Rules).Claims);
        var ledger = IngestLedger(atomizerId, oldAtom);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = currentText;
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = oldText;
        InstallLedger(fixture, ledger, oldAtom);
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, ledger, new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.Ingest(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains(
            "WARNING silent-zero-extraction source=fixture-source",
            result.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestCommitsReportedCoarseFallbackAndCasBlobThroughProductionEnvironment()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var malformedBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**未知 1.2(B)**。free-form source。\n");
        var malformedText = Encoding.UTF8.GetString(malformedBytes);
        var ledger = IngestLedger(atomizerId, oldAtom);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = malformedText;
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        fixture.Files[oldCapture.RelativePath] = Encoding.UTF8.GetString(oldCapture.Bytes.AsSpan());
        fixture.Baseline[oldCapture.RelativePath] = Encoding.UTF8.GetString(oldCapture.Bytes.AsSpan());
        InstallLedger(fixture, ledger, oldAtom);
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, ledger, new UTF8Encoding(false));
        var oldCasPath = Path.Combine(
            temporary.Path,
            oldCapture.RelativePath.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(Path.GetDirectoryName(oldCasPath)!);
        File.WriteAllBytes(oldCasPath, oldCapture.Bytes.AsSpan());
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.Ingest(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("coarse_fallbacks=1", result.Output, StringComparison.Ordinal);
        Assert.Contains(
            "INGEST_FALLBACK source=fixture-source",
            result.Output,
            StringComparison.Ordinal);
        Assert.Contains("cas_objects_written=1", result.Output, StringComparison.Ordinal);
        var written = BackfillInventoryLoader.Load(File.ReadAllText(outputPath));
        var coarse = Assert.Single(written.RequireDigestionEntries().Where(static entry =>
            entry.AstPath == "coarse/source"));
        Assert.Equal(coarse.Fingerprints.RawSha256, coarse.CasRef);
        var coarsePath = Path.Combine(
            temporary.Path,
            DigestionCasStore.RootPath.Replace('/', Path.DirectorySeparatorChar),
            coarse.CasRef["sha256:".Length..]);
        Assert.Equal(malformedBytes, File.ReadAllBytes(coarsePath));

        // The per-source line above is emitted before the status table, which runs to
        // thousands of lines, so on a terminal it is off-screen by the time the command
        // returns. A run that degraded a volume has to say so where a reader lands.
        var trailer = result.Output.TrimEnd('\n').Split('\n')[^1];
        Assert.Equal(
            "INGEST_INCOMPLETE 1 source registered without being atomised: fixture-source",
            trailer);
    }

    [Fact]
    public void IngestRollsBackNewCasObjectsWhenTheLedgerWriteFails()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。rewritten。\n\n**定理 1.2(B)**。new。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes, DigestionTestSupport.Rules).Claims);
        var ledger = IngestLedger(atomizerId, oldAtom);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        InstallLedger(fixture, ledger, oldAtom);
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(outputPath);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.Ingest(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("INGEST_INVALID", result.Error, StringComparison.Ordinal);
        var casRoot = Path.Combine(
            temporary.Path,
            DigestionCasStore.RootPath.Replace('/', Path.DirectorySeparatorChar));
        Assert.False(Directory.Exists(casRoot) && Directory.EnumerateFiles(casRoot).Any());
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
    public void IngestPreservesExactNoncanonicalStaleReceiptRepresentation()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes, DigestionTestSupport.Rules).Claims);
        var ledger = IngestLedger(atomizerId, oldAtom).Replace(
            "atom_id: old-receipt",
            "atom_id: \"old-receipt\"",
            StringComparison.Ordinal);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        InstallLedger(fixture, ledger, oldAtom);
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, ledger, new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.Ingest(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains(
            "atom_id: \"old-receipt\"",
            File.ReadAllText(outputPath),
            StringComparison.Ordinal);
    }

    [Fact]
    public void IngestMigratesLegacyBoundaryLedgerInOneStepAndIsIdempotent()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var oldBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。rewritten。\n\n**定理 1.2(B)**。new。\n");
        var oldAtom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, oldBytes, DigestionTestSupport.Rules).Claims);
        var legacyLedger = LegacyIngestLedger(atomizerId, oldAtom);
        fixture.Files[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[GoldenCorpus.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        InstallLedger(fixture, legacyLedger, oldAtom);
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, legacyLedger, new UTF8Encoding(false));
        var firstEnvironment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var first = firstEnvironment.Ingest(["--base", "baseline"]);

        Assert.True(first.Success, first.Error);
        Assert.Contains("stale_acknowledged=0", first.Output, StringComparison.Ordinal);
        Assert.Contains("residual_open_added=2", first.Output, StringComparison.Ordinal);
        Assert.Contains("ledger_changed=true", first.Output, StringComparison.Ordinal);
        var migratedText = File.ReadAllText(outputPath);
        Assert.DoesNotContain("boundary:", migratedText, StringComparison.Ordinal);
        var migrated = BackfillInventoryLoader.Load(migratedText);
        Assert.All(migrated.RequireDigestionEntries(), static entry => Assert.Null(entry.Boundary));
        fixture.Files[BackfillInventoryLoader.RelativePath] = migratedText;
        foreach (var entry in migrated.RequireDigestionEntries().Where(static entry =>
                     entry.AtomId != "old-receipt"))
        {
            var relativePath = DigestionCasStore.RootPath
                + entry.CasRef["sha256:".Length..];
            fixture.Files[relativePath] = File.ReadAllText(Path.Combine(
                temporary.Path,
                relativePath.Replace('/', Path.DirectorySeparatorChar)));
        }

        var secondEnvironment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var second = secondEnvironment.Ingest(["--base", "baseline"]);

        Assert.True(second.Success, second.Error);
        Assert.Contains("stale_acknowledged=0", second.Output, StringComparison.Ordinal);
        Assert.Contains("residual_open_added=0", second.Output, StringComparison.Ordinal);
        Assert.Contains("cas_objects_written=0", second.Output, StringComparison.Ordinal);
        Assert.Contains("ledger_changed=false", second.Output, StringComparison.Ordinal);
        Assert.Equal(migratedText, File.ReadAllText(outputPath));
    }

    private static string IngestLedger(string atomizerId, DigestionAtom atom) => $$"""
        schema_version: 3
        ledger: theory-digestion-v1
        sources:
          - source_id: fixture-source
            path: {{GoldenCorpus.FixtureDigestionSourcePath}}
            atomizer: {{atomizerId}}
            acknowledged_stale: []
            entries:
              - atom_id: old-receipt
                ast_path: {{atom.AstPath}}
                fingerprints:
                  raw_sha256: {{atom.Fingerprints.RawSha256}}
                  normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
                cas_ref: {{atom.Fingerprints.RawSha256}}
                coverage_gids: []
                receipts:
                  coverage: []
                  scribe: []
                  unresolved_subitems: []
                  chain_atoms: []
                  tail_authorization: null
                status:
                  migration: residual
                  truth: open
        ticket_index: []
        """;

    private static void InstallLedger(
        RuleFixture fixture,
        string ledger,
        DigestionAtom? existingAtom)
    {
        fixture.Files[BackfillInventoryLoader.RelativePath] = ledger;
        fixture.Baseline[BackfillInventoryLoader.RelativePath] = ledger;
        fixture.Files.Remove(GoldenCorpus.FixtureCasPath);
        fixture.Baseline.Remove(GoldenCorpus.FixtureCasPath);
        if (existingAtom is null)
        {
            return;
        }

        var captured = DigestionCasStore.Capture(existingAtom.RawBytes.AsSpan());
        var text = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
        fixture.Files[captured.RelativePath] = text;
        fixture.Baseline[captured.RelativePath] = text;
    }

    private static void InstallDirectoryLedger(
        RuleFixture fixture,
        string atomizerId,
        DigestionAtom atom)
    {
        InstallLedger(fixture, IngestLedger(atomizerId, atom), atom);
        fixture.Files.Remove(BackfillInventoryLoader.RelativePath);
        fixture.Baseline.Remove(BackfillInventoryLoader.RelativePath);
        var sourceMetadata = $"source_id = \"fixture-source\"\n"
            + $"path = \"{GoldenCorpus.FixtureDigestionSourcePath}\"\n"
            + $"atomizer = \"{atomizerId}\"\n";
        var atomText = DirectoryAtom(atom);
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[$"{BackfillInventoryLoader.RootPath}fixture-source/source.toml"] = sourceMetadata;
            files[DirectoryAtomPath("old-receipt", "residual-open")] = atomText;
            files[BackfillInventoryLoader.TicketIndexPath] = string.Empty;
        }
    }

    private static string DirectoryAtomPath(string atomId, string state) =>
        $"{BackfillInventoryLoader.RootPath}fixture-source/{state}/{atomId}.yaml";

    private static string DirectoryAtom(DigestionAtom atom) => $$"""
        ast_path: {{atom.AstPath}}
        fingerprints:
          raw_sha256: {{atom.Fingerprints.RawSha256}}
          normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
        cas_ref: {{atom.Fingerprints.RawSha256}}
        coverage_gids: []
        receipts:
          coverage: []
          scribe: []
          unresolved_subitems: []
        """;

    private static void WriteDirectoryLedger(
        string repositoryRoot,
        IReadOnlyDictionary<string, string> files)
    {
        foreach (var (path, text) in files.Where(static pair =>
                     BackfillInventoryLoader.IsCanonicalPath(pair.Key)))
        {
            var outputPath = Path.Combine(
                repositoryRoot,
                path.Replace('/', Path.DirectorySeparatorChar));
            Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
            File.WriteAllText(outputPath, text, new UTF8Encoding(false));
        }
    }

    private static string LegacyIngestLedger(string atomizerId, DigestionAtom atom) => $$"""
        schema_version: 3
        ledger: theory-digestion-v1
        sources:
          - source_id: fixture-source
            path: {{GoldenCorpus.FixtureDigestionSourcePath}}
            atomizer: {{atomizerId}}
            entries:
              - atom_id: old-receipt
                boundary:
                  ast_path: {{atom.AstPath}}
                  start_byte: {{atom.StartByte}}
                  end_byte: {{atom.EndByte}}
                fingerprints:
                  raw_sha256: {{atom.Fingerprints.RawSha256}}
                  normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
                cas_ref: {{atom.Fingerprints.RawSha256}}
                coverage_gids: []
                receipts:
                  coverage: []
                  scribe: []
                  unresolved_subitems: []
                  chain_atoms: []
                  tail_authorization: null
                status:
                  migration: residual
                  truth: open
        ticket_index: []
        """;
}
