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
    public void AlignDigestionStatusRefreshesCoverageTargetAndSecondRunIsByteIdentical()
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
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            FrozenStatementReceiptTestData.AddLedger(
                files,
                new FrozenStatementReceiptTestData.Module(
                    coverageGid + ".lean",
                    FrozenStatementReceiptTestData.Id('d'),
                    []));
        }
        InstallDirectoryLedger(fixture, atomizerId, atom);
        var oldPath = DirectoryAtomPath(AtomId(atom), "residual-open");
        var atomText = DirectoryAtom(atom).Replace(
            "coverage_gids: []",
            $"coverage_gids:\n  - gid: {coverageGid}\n    target_statement_id: null",
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
        Assert.Equal(
            FrozenStatementReceiptTestData.Resolve(fixture.Files, coverageGid),
            Assert.Single(entry.Coverage).TargetStatementId);
        var afterFirst = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        Assert.Contains(
            newPath
                + "\0"
                + Convert.ToBase64String(BackfillInventoryWriter.WriteAtom(entry).AsSpan())
                + "\n",
            afterFirst,
            StringComparison.Ordinal);
        var alignedFiles = new Dictionary<string, string>(fixture.Files, StringComparer.Ordinal);
        alignedFiles.Remove(oldPath);
        alignedFiles[newPath] = Encoding.UTF8.GetString(
            BackfillInventoryWriter.WriteAtom(entry).AsSpan());
        var secondEnvironment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(alignedFiles),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var second = secondEnvironment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.True(second.Success, second.Error);
        Assert.Contains("ledger_changed=false", second.Output, StringComparison.Ordinal);
        Assert.Equal(afterFirst, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    [Fact]
    public void AlignDigestionStatusConvergesMultiLevelChainAfterPinRepairInOneRun()
    {
        const string coverageGid = "D5/S0/Carrier/Ring";
        const string sourceId = "fixed-point-chain";
        var fixture = new RuleFixture();
        var definitionPath = ScribeEmissionAttestation.DefinitionPath(coverageGid);
        var emissionPath = ScribeEmissionAttestation.EmissionPath(coverageGid);
        var definitionHash = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(fixture.Files[definitionPath])).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(fixture.Files[emissionPath])).RawSha256;
        var targetStatementId = FrozenStatementReceiptTestData.Id('d');
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            FrozenStatementReceiptTestData.AddLedger(
                files,
                new FrozenStatementReceiptTestData.Module(
                    RuleFixture.RingPath,
                    targetStatementId,
                    []));
        }

        var atoms = new[] { "repair", "parent", "middle", "leaf" }
            .Select(name => DigestionAtom.FromFrozenCas(
                ImmutableArray.CreateRange(Encoding.UTF8.GetBytes($"fixed-point-{name}\n"))))
            .ToArray();
        var atomIds = atoms.Select(AtomId).ToArray();
        DigestionLedgerEntry Entry(int index, DigestionMigrationState migration, string? childId = null)
        {
            var receipt = new DigestionScribeReceipt(
                coverageGid,
                definitionHash,
                emissionHash);
            return DigestionTestSupport.Entry(
                atoms[index],
                atomIds[index],
                AtomizerRegistry.NoAtomizerId,
                migration,
                DigestionTruthState.Closed,
                [coverageGid],
                new DigestionReceipts(
                    [receipt],
                    [],
                    childId is null ? [] : [childId],
                    null),
                sourceId,
                RuleFixture.FixtureDigestionSourcePath) with
            {
                Coverage = [new DigestionCoverageEdge(coverageGid, targetStatementId)],
            };
        }

        var baselineEntries = new[]
        {
            Entry(0, DigestionMigrationState.Absorbed),
            Entry(1, DigestionMigrationState.Partial, atomIds[2]),
            Entry(2, DigestionMigrationState.Partial, atomIds[3]),
            Entry(3, DigestionMigrationState.Partial),
        };
        var baselineDocument = DigestionTestSupport.Document(
            AtomizerRegistry.NoAtomizerId,
            [.. baselineEntries],
            sourceId,
            RuleFixture.FixtureDigestionSourcePath);
        var currentEntries = baselineEntries.ToArray();
        currentEntries[0] = currentEntries[0] with
        {
            Coverage =
            [
                new DigestionCoverageEdge(
                    coverageGid,
                    "sha256:" + new string('0', 64)),
            ],
        };
        var currentDocument = baselineDocument.WithDigestionSources(
        [
            Assert.Single(baselineDocument.RequireDigestionSources()) with
            {
                Entries = [.. currentEntries],
            },
        ]);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Files, currentDocument);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Baseline, baselineDocument);
        foreach (var (atom, atomId) in atoms.Zip(atomIds))
        {
            var casPath = DigestionCasStore.RootPath + atomId;
            var bytes = Encoding.UTF8.GetString(atom.RawBytes.AsSpan());
            fixture.Files[casPath] = bytes;
            fixture.Baseline[casPath] = bytes;
        }

        var verified = VerifiedScribeEmissions.Create(
        [
            new ScribeEmissionRecord(
                coverageGid,
                definitionPath,
                definitionHash,
                emissionPath,
                emissionHash),
        ]);
        var repairPath = DirectoryAtomPath(sourceId, atomIds[0], "absorbed-closed");
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var first = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([repairPath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(verified));

        var firstResult = first.AlignDigestionStatus(["--base", "baseline"]);

        Assert.True(firstResult.Success, firstResult.Error);
        Assert.Contains("ledger_changed=true", firstResult.Output, StringComparison.Ordinal);
        var alignedDocument = BackfillInventoryLoader.LoadRoot(temporary.Path);
        var aligned = alignedDocument.RequireDigestionEntries();
        Assert.All(aligned, static entry =>
            Assert.Equal(DigestionMigrationState.Absorbed, entry.ProjectedStatus.Migration));
        var afterFirst = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var alignedFiles = new Dictionary<string, string>(fixture.Files, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(alignedFiles, alignedDocument);
        var statusMovePaths = new List<string>();
        foreach (var atomId in atomIds.Skip(1))
        {
            var oldPath = DirectoryAtomPath(sourceId, atomId, "partial-closed");
            var newPath = DirectoryAtomPath(sourceId, atomId, "absorbed-closed");
            statusMovePaths.Add(oldPath);
            statusMovePaths.Add(newPath);
        }

        var second = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(statusMovePaths),
                Snapshot(alignedFiles),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(verified));

        var secondResult = second.AlignDigestionStatus(["--base", "baseline"]);

        Assert.True(secondResult.Success, secondResult.Error);
        Assert.Contains("ledger_changed=false", secondResult.Output, StringComparison.Ordinal);
        Assert.Equal(afterFirst, DirectoryLedgerTestSupport.RepositoryImage(temporary));
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
    [InlineData("coverage-target-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void AlignRepairsCoverageButRejectsScribeIntegrityMismatchBeforeWritingLedger(
        string mismatchCode)
    {
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            UnrelatedSibling = new CoverUnrelatedSiblingSpec(
                ["D5/S0/Carrier/Probe.probe"],
                ["D5/S0/Carrier/Probe.probe"],
                []),
        });
        var inputs = DirectoryInputs(WithSiblingReceiptMismatch(materialized, mismatchCode));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        if (mismatchCode == "coverage-target-mismatch")
        {
            Assert.True(result.Success, result.Error);
            Assert.NotEqual(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        }
        else
        {
            Assert.False(result.Success);
            Assert.Contains("digest status is invalid", result.Error, StringComparison.Ordinal);
            Assert.Contains(mismatchCode, result.Error, StringComparison.Ordinal);
            Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        }
    }

    [Theory]
    [InlineData("coverage-target-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void AlignRepairsCoverageButRejectsScribeBacklogAtForkPoint(string mismatchCode)
    {
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            ReportDeclarations = ImmutableArray.Create("probe", "sibling"),
            UnrelatedSibling = new CoverUnrelatedSiblingSpec(
                ["D5/S0/Carrier/Probe.sibling"],
                ["D5/S0/Carrier/Probe.sibling"],
                []),
        });
        var inputs = DirectoryInputs(WithReceiptMismatchAtForkPoint(
            materialized,
            mismatchCode,
            byteIdenticalBaseline: true));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        if (mismatchCode == "coverage-target-mismatch")
        {
            Assert.True(result.Success, result.Error);
            Assert.NotEqual(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        }
        else
        {
            Assert.False(result.Success);
            Assert.Contains(mismatchCode, result.Error, StringComparison.Ordinal);
            Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        }
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

}
