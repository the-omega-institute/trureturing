using System.Collections.Immutable;
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
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        InstallDirectoryLedger(fixture, atomizerId, atom);
        using var temporary = new TemporaryDirectory();
        var atomPath = DirectoryAtomPath(AtomId(atom), "residual-open");
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

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("ledger_changed=false", result.Output, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(
            temporary.Path,
            BackfillInventoryLoader.RelativePath.Replace('/', Path.DirectorySeparatorChar))));
    }

    [Fact]
    public void ByteIdenticalIngestRejectsGenericChainWhoseParentHasNoClausePlan()
    {
        AssertByteIdenticalGenericChainIngestRejected("missing-child");
    }

    [Fact]
    public void ByteIdenticalIngestRejectsSelfReferentialGenericChainWhoseParentHasNoClausePlan()
    {
        AssertByteIdenticalGenericChainIngestRejected(chainAtomId: null);
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
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        InstallDirectoryLedger(fixture, atomizerId, atom);
        var oldPath = DirectoryAtomPath(AtomId(atom), "residual-open");
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

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        var newPath = DirectoryAtomPath(AtomId(atom), "partial-closed");
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
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        InstallDirectoryLedger(fixture, atomizerId, oldAtom);
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var existingPath = Path.Combine(
            temporary.Path,
            DirectoryAtomPath(AtomId(oldAtom), "residual-open")
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

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

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
            replacement);
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
        var ledger = MapOnlyEntry(IngestLedger(atomizerId, oldAtom), entry => entry with
        {
            ProjectedStatus = entry.ProjectedStatus with
            {
                Migration = DigestionMigrationState.Absorbed,
            },
        });
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        InstallProjectedLedger(fixture, ledger, oldAtom);
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

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("stale_acknowledged=0", result.Output, StringComparison.Ordinal);
        Assert.Contains("residual_open_added=2", result.Output, StringComparison.Ordinal);
        Assert.Contains("cas_objects_written=2", result.Output, StringComparison.Ordinal);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.Contains("DIGEST_STATUS entries=3", result.Output, StringComparison.Ordinal);
        var written = BackfillInventoryLoader.LoadRoot(temporary.Path);
        var source = Assert.Single(written.RequireDigestionSources());
        Assert.Empty(source.AcknowledgedStale);
        Assert.Equal(3, source.Entries.Length);
        Assert.Equal(
            DigestionMigrationState.Residual,
            source.Entries.Single(entry => entry.AtomId == AtomId(oldAtom)).ProjectedStatus.Migration);
        var casBacked = source.Entries.Where(entry => entry.AtomId != AtomId(oldAtom)).ToArray();
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

        Assert.True(File.Exists(Path.Combine(
            temporary.Path,
            DirectoryAtomPath(AtomId(oldAtom), "residual-open").Replace('/', Path.DirectorySeparatorChar))));
    }

    [Fact]
    public void IngestRejectsStructurallyInvalidLedgerWithoutWriting()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。claim。\n");
        var atom = Assert.Single(AtomizerRegistry.Atomize(atomizerId, sourceBytes, DigestionTestSupport.Rules).Claims);
        var ledger = IngestLedger(atomizerId, atom);
        var ledgerSource = Assert.Single(ledger.RequireDigestionSources());
        ledger = ledger.WithDigestionSources(
        [
            ledgerSource with
            {
                SourceId = "INVALID",
                Entries = ledgerSource.Entries.Select(entry => entry with
                {
                    SourceId = "INVALID",
                }).ToImmutableArray(),
            },
        ]);
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        InstallProjectedLedger(fixture, ledger, atom);
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var outputPath = Path.Combine(
            temporary.Path,
            $"{BackfillInventoryLoader.RootPath}INVALID/source.toml"
                .Replace('/', Path.DirectorySeparatorChar));
        var before = File.ReadAllText(outputPath);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("invalid source_id: INVALID", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, File.ReadAllText(outputPath));
    }

    [Theory]
    [InlineData("coverage-receipt-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void IngestRejectsEachReceiptIntegrityMismatchBeforeWritingLedger(string mismatchCode)
    {
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            OtherAtomGid = "D5/S0/Carrier/Probe.probe",
        });
        var inputs = DirectoryInputs(WithSiblingReceiptMismatch(materialized, mismatchCode));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("digest status is invalid", result.Error, StringComparison.Ordinal);
        Assert.Contains(mismatchCode, result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    [Theory]
    [InlineData("coverage-receipt-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void IngestRejectsNoOpWhenReceiptIntegrityBacklogExistsAtForkPoint(string mismatchCode)
    {
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            OtherAtomGid = "D5/S0/Carrier/Probe.sibling",
            ReportDeclarations = ImmutableArray.Create("probe", "sibling"),
        });
        var inputs = DirectoryInputs(WithReceiptMismatchAtForkPoint(
            materialized,
            mismatchCode,
            byteIdenticalBaseline: true));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains(mismatchCode, result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    [Fact]
    public void IngestPerformsFirstExtractionForRegisteredEmptySource()
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceText = "# Synthetic\n\n**定理 1.1(A)**。claim。\n";
        var ledger = DigestionTestSupport.Document(
            atomizerId,
            [],
            "fixture-source",
            RuleFixture.FixtureDigestionSourcePath,
            GenreRegistryCheck.Collected([]));
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = sourceText;
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = sourceText;
        InstallProjectedLedger(fixture, ledger, existingAtom: null);
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

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        var written = BackfillInventoryLoader.LoadRoot(temporary.Path);
        Assert.Single(written.RequireDigestionEntries());
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
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = currentText;
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = oldText;
        InstallProjectedLedger(fixture, ledger, oldAtom);
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

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

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
        // Prose the atomizer recognizes nothing in is still a live coarse trigger. An unregistered
        // genre token is not: the aligner can name and refuse that specific unsupported input.
        var malformedBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n没有任何编号抬头的自由散文。\n");
        var malformedText = Encoding.UTF8.GetString(malformedBytes);
        var ledger = DigestionTestSupport.Document(
            atomizerId,
            [],
            "fixture-source",
            RuleFixture.FixtureDigestionSourcePath,
            GenreRegistryCheck.Collected([]));
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = malformedText;
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = malformedText;
        InstallProjectedLedger(fixture, ledger, existingAtom: null);
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

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("coarse_fallbacks=1", result.Output, StringComparison.Ordinal);
        Assert.Contains(
            "INGEST_FALLBACK source=fixture-source",
            result.Output,
            StringComparison.Ordinal);
        Assert.Contains("cas_objects_written=1", result.Output, StringComparison.Ordinal);
        var written = BackfillInventoryLoader.LoadRoot(temporary.Path);
        var coarse = Assert.Single(written.RequireDigestionEntries().Where(entry =>
            entry.Fingerprints.RawSha256 == DigestionFingerprint.Compute(malformedBytes).RawSha256));
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
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(currentBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(oldBytes);
        InstallProjectedLedger(fixture, ledger, oldAtom);
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(
            temporary.Path,
            $"{BackfillInventoryLoader.RootPath}fixture-source/source.toml"
                .Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(outputPath);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("INGEST_INVALID", result.Error, StringComparison.Ordinal);
        var casRoot = Path.Combine(
            temporary.Path,
            DigestionCasStore.RootPath.Replace('/', Path.DirectorySeparatorChar));
        Assert.False(Directory.Exists(casRoot) && Directory.EnumerateFiles(casRoot).Any());
    }

    private static BackfillInventoryDocument IngestLedger(string atomizerId, DigestionAtom atom) =>
        BuildIngestLedger(atomizerId, atom);

    private static BackfillInventoryDocument MapOnlyEntry(
        BackfillInventoryDocument document,
        Func<DigestionLedgerEntry, DigestionLedgerEntry> map)
    {
        var source = Assert.Single(document.RequireDigestionSources());
        return document.WithDigestionSources(
        [
            source with { Entries = [map(Assert.Single(source.Entries))] },
        ]);
    }

    private static void AssertByteIdenticalGenericChainIngestRejected(string? chainAtomId)
    {
        var fixture = new RuleFixture();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceBytes = Encoding.UTF8.GetBytes("# Synthetic\n\n**定理 1.1(A)**。claim。\n");
        var atom = Assert.Single(AtomizerRegistry.Atomize(
            atomizerId,
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var atomId = AtomId(atom);
        chainAtomId ??= atomId;
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        InstallDirectoryLedger(fixture, atomizerId, atom);
        var atomPath = DirectoryAtomPath(atomId, "residual-open");
        var atomText = fixture.Files[atomPath].Replace(
            "  unresolved_subitems: []",
            $"  unresolved_subitems: []\n  chain_atoms:\n    - {chainAtomId}",
            StringComparison.Ordinal);
        fixture.Files[atomPath] = atomText;
        fixture.Baseline[atomPath] = atomText;
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var outputPath = Path.Combine(
            temporary.Path,
            atomPath.Replace('/', Path.DirectorySeparatorChar));
        var unchangedWriteTime = new DateTime(2000, 1, 1, 0, 0, 0, DateTimeKind.Utc);
        File.SetLastWriteTimeUtc(outputPath, unchangedWriteTime);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains(
            $"INGEST_INVALID ingest clause chain parent {atomId} lacks verified clause-plan proof: "
                + $"entry {atomId} malformed clause chain: parent CAS blob has no clause plan",
            result.Error,
            StringComparison.Ordinal);
        Assert.Equal(atomText, TemporaryFileSystem.File.ReadAllText(outputPath));
        Assert.Equal(unchangedWriteTime, File.GetLastWriteTimeUtc(outputPath));
    }

    private static void InstallDirectoryLedger(
        RuleFixture fixture,
        string atomizerId,
        DigestionAtom atom) =>
        InstallProjectedLedger(fixture, IngestLedger(atomizerId, atom), atom);

    private static void InstallProjectedLedger(
        RuleFixture fixture,
        BackfillInventoryDocument ledger,
        DigestionAtom? existingAtom)
    {
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            DirectoryLedgerTestSupport.ReplaceWithProjection(files, ledger);
        }

        fixture.Files.Remove(RuleFixture.FixtureCasPath);
        fixture.Baseline.Remove(RuleFixture.FixtureCasPath);
        if (existingAtom is null)
        {
            return;
        }

        var captured = DigestionCasStore.Capture(existingAtom.RawBytes.AsSpan());
        var text = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
        fixture.Files[captured.RelativePath] = text;
        fixture.Baseline[captured.RelativePath] = text;
    }

    private static string DirectoryAtomPath(string atomId, string state) =>
        $"{BackfillInventoryLoader.RootPath}fixture-source/{state}/{atomId}.yaml";

    private static string AtomId(DigestionAtom atom) =>
        atom.Fingerprints.RawSha256["sha256:".Length..];

    private static string DirectoryAtom(DigestionAtom atom) => $$"""
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

    private static BackfillInventoryDocument BuildIngestLedger(
        string atomizerId,
        DigestionAtom atom)
    {
        var entry = DigestionTestSupport.Entry(
            atom,
            AtomId(atom),
            atomizerId,
            sourceId: "fixture-source",
            sourcePath: RuleFixture.FixtureDigestionSourcePath);
        return DigestionTestSupport.Document(
            atomizerId,
            [entry],
            "fixture-source",
            RuleFixture.FixtureDigestionSourcePath,
            atomizerId == AtomizerRegistry.NoAtomizerId
                ? GenreRegistryCheck.NoGenreRegistry
                : GenreRegistryCheck.Collected([]));
    }

    /// <summary>
    /// SL-003 的 conservative-unknown 判据按<b>语法</b>识别 receiver:对临时夹具变量路径的
    /// File.ReadAllText 会被记为 VariablePath。这里的包装让该读取显式归属于临时文件系统,
    /// 与 EmitFormalizationReceiptTests / TruthReleaseBundleWriterTests 的同形处置一致。
    /// </summary>
    private static class TemporaryFileSystem
    {
        internal static class File
        {
            internal static string ReadAllText(string path) => System.IO.File.ReadAllText(path);
        }
    }

}
