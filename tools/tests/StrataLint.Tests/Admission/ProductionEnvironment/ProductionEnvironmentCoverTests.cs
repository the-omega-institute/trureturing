using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests(Xunit.Abstractions.ITestOutputHelper output)
{
    [Fact]
    public void CoverAtomReadsAndMovesTheDirectoryFormDigestionLedgerAtom()
    {
        var inputs = CoverWorld.Materialize(new CoverSpec());
        var directoryInputs = inputs with
        {
            Files = DirectoryLedgerTestSupport.Project(inputs.Files),
            Baseline = DirectoryLedgerTestSupport.Project(inputs.Baseline),
        };
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, directoryInputs.Files);
        var reportSource = new FakeLeanReportSource(directoryInputs.Report);
        var currentReadCount = 0;
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                current: null,
                CoverWorld.Raw(directoryInputs.Baseline),
                currentReader: () => CoverWorld.Raw(
                    currentReadCount++ == 0
                        ? directoryInputs.Files
                        : FilesWithLedgerFromRoot(directoryInputs.Files, temporary.Path))),
            reportSource,
            new FakeScribeEmissionVerifier(directoryInputs.VerifiedEmissions));

        var result = environment.CoverAtom(CoverArgs(directoryInputs));

        Assert.True(result.Success, result.Error);
        Assert.Equal(1, reportSource.CallCount);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        var oldPath = Path.Combine(
            temporary.Path,
            BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar),
            "fixture-source",
            "residual-open",
            CoverWorld.DefaultAtomId + ".yaml");
        var newPath = Path.Combine(
            temporary.Path,
            BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar),
            "fixture-source",
            "absorbed-closed",
            CoverWorld.DefaultAtomId + ".yaml");
        Assert.False(File.Exists(oldPath));
        Assert.True(File.Exists(newPath));
        var entry = Assert.Single(
            BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        Assert.Equal([inputs.Gid], entry.CoverageGids.ToArray());
        Assert.False(File.Exists(Path.Combine(
            temporary.Path,
            BackfillInventoryLoader.RelativePath.Replace('/', Path.DirectorySeparatorChar))));
        AssertProductionScribeVerifierMaterializesOnlyTheCapturedSnapshot();
    }

    [Fact]
    public void CoverAtomDiffDoesNotRequireBaselineGenreProjection()
    {
        var inputs = DirectoryInputs(CoverWorld.Materialize(new CoverSpec()));
        var historicalBaseline = new Dictionary<string, string>(inputs.Baseline, StringComparer.Ordinal);
        var metadata = Assert.Single(historicalBaseline, static pair =>
            pair.Key.EndsWith("/source.toml", StringComparison.Ordinal));
        historicalBaseline[metadata.Key] = metadata.Value
            .Replace("genre_registry_check = \"collected\"\n", string.Empty, StringComparison.Ordinal)
            .Replace("unregistered_genres = []\n", string.Empty, StringComparison.Ordinal);
        inputs = inputs with { Baseline = historicalBaseline };
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.CoverAtom(CoverArgs(inputs));

        Assert.True(result.Success, result.Error);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void CoverAtomRejectsDriftInUnchangedDirectoryLedgerMetadata()
    {
        var inputs = CoverWorld.Materialize(new CoverSpec());
        var directoryInputs = inputs with
        {
            Files = DirectoryLedgerTestSupport.Project(inputs.Files),
            Baseline = DirectoryLedgerTestSupport.Project(inputs.Baseline),
        };
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, directoryInputs.Files);
        var metadata = Assert.Single(directoryInputs.Files, static pair =>
            pair.Key.EndsWith("/source.toml", StringComparison.Ordinal));
        var metadataPath = Path.Combine(
            temporary.Path,
            metadata.Key.Replace('/', Path.DirectorySeparatorChar));
        var concurrent = metadata.Value + "\n";
        File.WriteAllText(metadataPath, concurrent, new UTF8Encoding(false));
        var environment = BuildCoverEnvironment(
            temporary.Path,
            directoryInputs,
            directoryInputs.Files);

        var result = environment.CoverAtom(CoverArgs(directoryInputs));

        Assert.False(result.Success);
        Assert.Contains("changed under us", result.Error, StringComparison.Ordinal);
        Assert.Equal(concurrent, File.ReadAllText(metadataPath));
    }

    [Theory]
    [InlineData("coverage-target-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void DigestStatusRejectsCoverageMismatchButAcceptsScribeByteMismatch(string mismatchCode)
    {
        var inputs = DirectoryInputs(CoverWorld.Materialize(CoverWorld.StaleReceiptSpec()));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var alignedFiles = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal);
        var verification = inputs.VerifiedEmissions
            ?? throw new InvalidOperationException("cover fixture omitted Scribe verification");
        if (mismatchCode == "coverage-target-mismatch")
        {
            var driftedDocument = MapOnlyEntry(
                BackfillInventoryLoader.LoadRoot(temporary.Path),
                entry => entry with
                {
                    Coverage = entry.Coverage.Select(receipt => receipt with
                    {
                        TargetStatementId = "sha256:" + new string('c', 64),
                    }).ToImmutableArray(),
                });
            DirectoryLedgerTestSupport.ReplaceWithProjection(alignedFiles, driftedDocument);
        }
        else
        {
            var documentGid = inputs.Gid[..inputs.Gid.LastIndexOf('.')];
            Assert.True(verification.TryGet(documentGid, out var record));
            var changedContent = Encoding.UTF8.GetBytes($"independent {mismatchCode}\n");
            var changedHash = DigestionFingerprint.Compute(changedContent).RawSha256;
            if (mismatchCode == "scribe-definition-mismatch")
            {
                alignedFiles[record.DefinitionPath] = Encoding.UTF8.GetString(changedContent);
                record = record with { DefinitionSha256 = changedHash };
            }
            else
            {
                alignedFiles[record.EmissionPath] = Encoding.UTF8.GetString(changedContent);
                record = record with { EmissionSha256 = changedHash };
            }

            verification = VerifiedScribeEmissions.Create([record], [inputs.Gid]);
        }

        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(alignedFiles),
                CoverWorld.Raw(inputs.Baseline)),
            new FakeLeanReportSource(inputs.Report),
            new FakeScribeEmissionVerifier(verification));

        var result = environment.DigestStatus(Array.Empty<string>());

        if (mismatchCode == "coverage-target-mismatch")
        {
            Assert.False(result.Success);
            Assert.Contains(mismatchCode, result.Error, StringComparison.Ordinal);
        }
        else
        {
            Assert.True(result.Success, result.Error);
            Assert.DoesNotContain(mismatchCode, result.Output, StringComparison.Ordinal);
        }
        foreach (var otherCode in new[]
                 {
                     "coverage-target-mismatch",
                     "scribe-definition-mismatch",
                     "scribe-emission-mismatch",
                 }.Where(code => code != mismatchCode))
        {
            Assert.DoesNotContain(otherCode, result.Error, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void CoverAtomWritesCoverageAndRecomputesDigestStatusThroughProductionEnvironment()
    {
        var inputs = DirectoryInputs(CoverWorld.Materialize(new CoverSpec()));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.CoverAtom(CoverArgs(inputs));

        Assert.True(result.Success, result.Error);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.Contains("DIGEST_STATUS", result.Output, StringComparison.Ordinal);
        var written = BackfillInventoryLoader.LoadRoot(temporary.Path);
        var entry = Assert.Single(
            written.RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        Assert.Equal(["D5/S0/Carrier/Probe.probe"], entry.CoverageGids.ToArray());
        Assert.Equal(DigestionMigrationState.Absorbed, entry.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, entry.ProjectedStatus.Truth);
    }

    [Fact]
    public void CoverAtomWithoutScribeKeyMovesCleanInheritedResidualOpenAtomToDeletableAbsorbedClosed()
    {
        var inputs = DirectoryInputs(CoverWorld.Materialize(new CoverSpec()));
        const string sourceAfterHistoricalAtom =
            "# Synthetic\n\n**定理 2.1(A)**。replacement fixture atom body。\n";
        inputs.Files[RuleFixture.FixtureDigestionSourcePath] = sourceAfterHistoricalAtom;
        inputs.Baseline[RuleFixture.FixtureDigestionSourcePath] = sourceAfterHistoricalAtom;
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var before = environment.DigestStatus(["--base", "baseline"]);
        Assert.True(before.Success, before.Error);
        output.WriteLine("BEFORE\n" + before.Output);
        Assert.Contains("deletable_now=0", before.Output, StringComparison.Ordinal);
        Assert.Contains("residual-open", before.Output, StringComparison.Ordinal);
        var console = new BufferedConsole();
        var exitCode = CliApplication.Run(["cover-atom", .. CoverArgs(inputs)], environment, console);
        output.WriteLine("COVER exit=" + exitCode + "\n" + console.Output + console.Error);
        Assert.Equal(0, exitCode);
        var result = new CommandResult(true, console.Output, console.Error);
        Assert.Contains("deletable=true", result.Output, StringComparison.Ordinal);
        var entry = Assert.Single(
            BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        Assert.Equal([inputs.Gid], entry.CoverageGids.ToArray());
        Assert.Single(entry.Coverage);
        Assert.Empty(entry.Receipts.Scribe);
        Assert.Equal(DigestionMigrationState.Absorbed, entry.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, entry.ProjectedStatus.Truth);
        var ledgerRoot = Path.Combine(
            temporary.Path,
            BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar),
            "fixture-source");
        Assert.False(File.Exists(Path.Combine(
            ledgerRoot,
            "residual-open",
            CoverWorld.DefaultAtomId + ".yaml")));
        Assert.True(File.Exists(Path.Combine(
            ledgerRoot,
            "absorbed-closed",
            CoverWorld.DefaultAtomId + ".yaml")));
        var persistedPath = Path.Combine(ledgerRoot, "absorbed-closed", CoverWorld.DefaultAtomId + ".yaml");
        var persisted = File.ReadAllText(persistedPath);
        Assert.DoesNotContain("scribe", persisted, StringComparison.Ordinal);
        output.WriteLine("PERSISTED\n" + persisted);
        var afterFiles = FilesWithLedgerFromRoot(inputs.Files, temporary.Path);
        var after = BuildCoverEnvironment(temporary.Path, inputs, afterFiles)
            .DigestStatus(["--base", "baseline"]);
        Assert.True(after.Success, after.Error);
        output.WriteLine("AFTER\n" + after.Output);
        Assert.Contains("deletable_now=1", after.Output, StringComparison.Ordinal);
        Assert.Contains("absorbed-closed", after.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("GAP ", after.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void CoverAtomReplayIsByteIdenticalAndSecondRunIsRejected()
    {
        var inputs = DirectoryInputs(CoverWorld.Materialize(new CoverSpec()));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);

        var first = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files)
            .CoverAtom(CoverArgs(inputs));

        Assert.True(first.Success, first.Error);
        var afterFirst = DirectoryLedgerTestSupport.Image(temporary.Path);
        Assert.NotEqual(before, afterFirst);

        var replayFiles = FilesWithLedgerFromRoot(inputs.Files, temporary.Path);
        var second = BuildCoverEnvironment(temporary.Path, inputs, replayFiles)
            .CoverAtom(CoverArgs(inputs));

        Assert.False(second.Success);
        Assert.Contains("already has coverage", second.Error, StringComparison.Ordinal);
        Assert.Equal(afterFirst, DirectoryLedgerTestSupport.Image(temporary.Path));
    }
}
