using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
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

        var result = environment.CoverAtom([.. CoverArgs(directoryInputs), "--align-scribe-receipt"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains(
            "COVER_ATOM_ALIGNED cover=passed align=passed",
            result.Output,
            StringComparison.Ordinal);
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
        AssertAlignedCoverRepairsPersistedScribeReceipt();
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
    [InlineData("probe")]
    [InlineData(null)]
    public void AlignScribeReceiptIsReachableThroughProductionCliDispatch(string? declaration)
    {
        var spec = CoverWorld.StaleReceiptSpec() with { Declaration = declaration };
        var inputs = CoverWorld.Materialize(spec with { InitialCoverage = [spec.Gid] });
        var directoryInputs = DirectoryInputs(inputs);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, directoryInputs.Files);
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["align-scribe-receipt", .. CoverWorld.AlignArgs(inputs)],
            CoverWorld.Environment(temporary.Path, directoryInputs, directoryInputs.Files),
            console);

        Assert.True(exitCode == 0, console.Error);
        Assert.Contains("ALIGN_SCRIBE_RECEIPT", console.Output, StringComparison.Ordinal);
        Assert.Equal(string.Empty, console.Error);
    }

    [Fact]
    public void RootUsageListsAlignScribeReceipt()
    {
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            Array.Empty<string>(),
            new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused")),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("align-scribe-receipt", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void AlignRemovesMismatchAndDefinitionDriftIsDetectedAgain()
    {
        var materialized = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec());
        var inputs = DirectoryInputs(materialized);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var initialEnvironment = CoverWorld.Environment(temporary.Path, inputs, inputs.Files);

        var before = initialEnvironment.DigestStatus(Array.Empty<string>());
        Assert.False(before.Success);
        Assert.Contains("scribe-definition-mismatch", before.Error, StringComparison.Ordinal);
        Assert.Contains("scribe-emission-mismatch", before.Error, StringComparison.Ordinal);

        var aligned = initialEnvironment.AlignScribeReceipt(CoverWorld.AlignArgs(inputs));
        Assert.True(aligned.Success, aligned.Error);
        var alignedFiles = FilesWithLedgerFromRoot(inputs.Files, temporary.Path);
        var after = CoverWorld.Environment(temporary.Path, inputs, alignedFiles)
            .DigestStatus(Array.Empty<string>());
        Assert.True(after.Success, after.Error);
        Assert.DoesNotContain("scribe-definition-mismatch", after.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("scribe-emission-mismatch", after.Output, StringComparison.Ordinal);

        var changedDefinition = "changed scribe definition\n";
        alignedFiles[ScribeEmissionAttestation.DefinitionPath(inputs.Gid[..inputs.Gid.LastIndexOf('.')])] =
            changedDefinition;
        Assert.True(inputs.VerifiedEmissions!.TryGet(
            inputs.Gid[..inputs.Gid.LastIndexOf('.')], out var oldRecord));
        var changedRecord = oldRecord with
        {
            DefinitionSha256 = DigestionFingerprint.Compute(
                Encoding.UTF8.GetBytes(changedDefinition)).RawSha256,
        };
        var changedVerification = VerifiedScribeEmissions.Create([changedRecord], [inputs.Gid]);
        var driftEnvironment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(alignedFiles),
                CoverWorld.Raw(inputs.Baseline)),
            new FakeLeanReportSource(inputs.Report),
            new FakeScribeEmissionVerifier(changedVerification));

        var drifted = driftEnvironment.DigestStatus(Array.Empty<string>());

        Assert.False(drifted.Success);
        Assert.Contains("scribe-definition-mismatch", drifted.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void AlignRejectsCoverageReceiptMismatchBeforeWritingLedger()
    {
        var inputs = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec() with
        {
            BaselineTargetIdentical = true,
        });
        var entry = Assert.Single(
            inputs.Document.RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        var oldCoverage = Assert.Single(entry.Coverage);
        var source = Assert.Single(inputs.Document.RequireDigestionSources());
        var driftedDocument = inputs.Document.WithDigestionSources(
        [
            source with
            {
                Entries = source.Entries.Select(candidate => candidate.AtomId == entry.AtomId
                    ? candidate with
                    {
                        Coverage =
                        [
                            oldCoverage with
                            {
                                TargetStatementId = "sha256:" + new string('c', 64),
                            },
                        ],
                    }
                    : candidate).ToImmutableArray(),
            },
        ]);
        var driftedFiles = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(driftedFiles, driftedDocument);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, driftedFiles);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["align-scribe-receipt", .. CoverWorld.AlignArgs(inputs)],
            CoverWorld.Environment(temporary.Path, inputs, driftedFiles),
            console);

        Assert.Equal(2, exitCode);
        Assert.Equal(string.Empty, console.Output);
        Assert.Contains("coverage-target-mismatch", console.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    [Theory]
    [InlineData("coverage-target-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void DigestStatusRejectsEachReceiptIntegrityMismatchIndependently(string mismatchCode)
    {
        var inputs = DirectoryInputs(CoverWorld.Materialize(CoverWorld.StaleReceiptSpec()));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var initialEnvironment = CoverWorld.Environment(temporary.Path, inputs, inputs.Files);

        var aligned = initialEnvironment.AlignScribeReceipt(CoverWorld.AlignArgs(inputs));

        Assert.True(aligned.Success, aligned.Error);
        var alignedFiles = FilesWithLedgerFromRoot(inputs.Files, temporary.Path);
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

        Assert.False(result.Success);
        Assert.Contains(mismatchCode, result.Error, StringComparison.Ordinal);
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
    public void AlignFailsClosedWhenTargetScribeMismatchRemainsAfterAlignment()
    {
        var inputs = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec());
        var directoryInputs = DirectoryInputs(inputs);
        Assert.True(inputs.VerifiedEmissions!.TryGet(
            inputs.Gid[..inputs.Gid.LastIndexOf('.')], out var verifiedRecord));
        var inconsistentVerification = VerifiedScribeEmissions.Create(
            [verifiedRecord with { DefinitionSha256 = "sha256:" + new string('c', 64) }],
            [inputs.Gid]);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, directoryInputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(directoryInputs.Files),
                CoverWorld.Raw(directoryInputs.Baseline)),
            new FakeLeanReportSource(inputs.Report),
            new FakeScribeEmissionVerifier(inconsistentVerification));

        var result = environment.AlignScribeReceipt(CoverWorld.AlignArgs(inputs));

        Assert.False(result.Success);
        Assert.Contains("scribe-definition-mismatch", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));

        // Extend this already-paid repository-read test: the map budget is structural and must
        // not be raised merely to add another representative of the same Scribe rule.
        AssertProductionScribeVerifierMaterializesOnlyTheCapturedSnapshot();
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
    public void CoverAtomWithReceiptsMovesCleanInheritedResidualOpenAtomToDeletableAbsorbedClosed()
    {
        var inputs = DirectoryInputs(CoverWorld.Materialize(new CoverSpec()));
        const string sourceAfterHistoricalAtom =
            "# Synthetic\n\n**定理 2.1(A)**。replacement fixture atom body。\n";
        inputs.Files[RuleFixture.FixtureDigestionSourcePath] = sourceAfterHistoricalAtom;
        inputs.Baseline[RuleFixture.FixtureDigestionSourcePath] = sourceAfterHistoricalAtom;
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.CoverAtom(CoverArgs(inputs));

        Assert.True(result.Success, result.Error);
        Assert.Contains("deletable=true", result.Output, StringComparison.Ordinal);
        var entry = Assert.Single(
            BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        Assert.Equal([inputs.Gid], entry.CoverageGids.ToArray());
        Assert.Single(entry.Coverage);
        Assert.Single(entry.Receipts.Scribe);
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
    }

    [Theory]
    [InlineData("coverage-target-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void AlignScribeReceiptRejectsReceiptIntegrityMismatchOnSiblingBeforeWritingLedger(
        string mismatchCode)
    {
        var materialized = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec() with
        {
            OtherAtomGid = "D5/S0/Carrier/Probe.probe",
        });
        var inputs = DirectoryInputs(WithSiblingReceiptMismatch(materialized, mismatchCode));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.AlignScribeReceipt(CoverWorld.AlignArgs(inputs));

        Assert.False(result.Success);
        Assert.Contains("digest status is invalid", result.Error, StringComparison.Ordinal);
        Assert.Contains(mismatchCode, result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    [Theory]
    [InlineData("coverage-target-mismatch", "probe")]
    [InlineData("scribe-definition-mismatch", "probe")]
    [InlineData("scribe-emission-mismatch", "probe")]
    [InlineData("coverage-target-mismatch", null)]
    [InlineData("scribe-definition-mismatch", null)]
    [InlineData("scribe-emission-mismatch", null)]
    public void AlignScribeReceiptRejectsTargetRepairWhenUnrelatedBacklogExistsAtBaseline(
        string mismatchCode,
        string? declaration)
    {
        var spec = CoverWorld.StaleReceiptSpec() with
        {
            Declaration = declaration,
            OtherAtomGid = "D5/S0/Carrier/Probe.sibling",
            ReportDeclarations = ImmutableArray.Create("probe", "sibling"),
        };
        var materialized = CoverWorld.Materialize(spec with { InitialCoverage = [spec.Gid] });
        var inputs = DirectoryInputs(WithReceiptMismatchAtBaseline(
            materialized,
            mismatchCode,
            byteIdenticalBaseline: true));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.AlignScribeReceipt(CoverWorld.AlignArgs(inputs));

        Assert.False(result.Success);
        Assert.Contains(mismatchCode, result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }

    [Fact]
    public void CoverAtomRejectsSiblingEvaluationFindingBeforeWritingLedger()
    {
        var materialized = CoverWorld.Materialize(new CoverSpec
        {
            OtherAtomGid = "D5/S0/Carrier/Probe.probe",
        });
        var inputs = DirectoryInputs(WithSiblingDuplicateCoverageReceipt(materialized));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.CoverAtom(CoverArgs(inputs));

        Assert.False(result.Success);
        Assert.Contains("digest status is invalid", result.Error, StringComparison.Ordinal);
        Assert.Contains("duplicate receipt", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
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
