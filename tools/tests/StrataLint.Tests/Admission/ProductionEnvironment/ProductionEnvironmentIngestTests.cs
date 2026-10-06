using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void AlignReadsTheDirectoryFormDigestionLedger()
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

        var result = environment.AlignDigestionStatus([]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("ledger_files_changed=0", result.Output, StringComparison.Ordinal);
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
    public void AlignDigestionStatusWithoutScribeReceiptsRefreshesCoverageTargetAndSecondRunIsByteIdentical()
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

        var result = environment.AlignDigestionStatus([]);

        Assert.True(result.Success, result.Error);
        var newPath = DirectoryAtomPath(AtomId(atom), "absorbed-closed");
        Assert.False(File.Exists(Path.Combine(
            temporary.Path,
            oldPath.Replace('/', Path.DirectorySeparatorChar))));
        var outputPath = Path.Combine(
            temporary.Path,
            newPath.Replace('/', Path.DirectorySeparatorChar));
        Assert.True(File.Exists(outputPath));
        var entry = Assert.Single(BackfillInventoryLoader.LoadRoot(temporary.Path)
            .RequireDigestionEntries());
        Assert.Equal(DigestionMigrationState.Absorbed, entry.ProjectedStatus.Migration);
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

        var second = secondEnvironment.AlignDigestionStatus([]);

        Assert.True(second.Success, second.Error);
        Assert.Contains("status_changed=0 coverage_retargeted=0 ledger_files_changed=0", second.Output, StringComparison.Ordinal);
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
            return DigestionTestSupport.Entry(
                atoms[index],
                atomIds[index],
                AtomizerRegistry.NoAtomizerId,
                migration,
                DigestionTruthState.Closed,
                [coverageGid],
                new DigestionReceipts(
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
        fixture.Files[repairPath] += "\n# preserve captured preimage bytes\r\n";
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

        var plan = first.AlignDigestionStatus(["--plan"]);
        Assert.True(plan.Success, plan.Error);
        Assert.Contains($"status_changed={atomIds.Length - 1} ", plan.Output, StringComparison.Ordinal);
        foreach (var atomId in atomIds.Skip(1))
        {
            Assert.Contains(
                $"ALIGN_ENTRY source={sourceId} atom={atomId} from=partial-closed to=absorbed-closed\n",
                plan.Output,
                StringComparison.Ordinal);
        }

        var firstResult = first.AlignDigestionStatus([]);

        Assert.True(firstResult.Success, firstResult.Error);
        Assert.Equal(plan.Output.Replace("applied=false", "applied=true", StringComparison.Ordinal), firstResult.Output);
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

        var secondResult = second.AlignDigestionStatus([]);

        Assert.True(secondResult.Success, secondResult.Error);
        Assert.Contains("status_changed=0 coverage_retargeted=0 ledger_files_changed=0", secondResult.Output, StringComparison.Ordinal);
        Assert.Equal(afterFirst, DirectoryLedgerTestSupport.RepositoryImage(temporary));
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

    [Theory]
    [InlineData("coverage-target-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void AlignRepairsCoverageAndAcceptsScribeByteBacklogAtBaseline(string mismatchCode)
    {
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            ReportDeclarations = ImmutableArray.Create("probe", "sibling"),
            UnrelatedSibling = new CoverUnrelatedSiblingSpec(
                ["D5/S0/Carrier/Probe.sibling"],
                ["D5/S0/Carrier/Probe.sibling"],
                []),
        });
        var inputs = DirectoryInputs(WithReceiptMismatchAtBaseline(
            materialized,
            mismatchCode,
            byteIdenticalBaseline: true));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.AlignDigestionStatus([]);

        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain(mismatchCode, result.Error, StringComparison.Ordinal);
        Assert.NotEqual(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        var sibling = Assert.Single(BackfillInventoryLoader.LoadRoot(temporary.Path)
            .RequireDigestionEntries(), entry => entry.AtomId == CoverWorld.UnrelatedAtomId);
        Assert.Equal(DigestionMigrationState.Absorbed, sibling.ProjectedStatus.Migration);
    }

}
