using System.Collections.Immutable;
using System.Text;
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
        var environment = BuildCoverEnvironment(
            temporary.Path,
            directoryInputs,
            directoryInputs.Files);

        var result = environment.CoverAtom(CoverArgs(directoryInputs));

        Assert.True(result.Success, result.Error);
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

    [Fact]
    public void AlignScribeReceiptIsReachableThroughProductionCliDispatch()
    {
        var inputs = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec());
        var directoryInputs = DirectoryInputs(inputs);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, directoryInputs.Files);
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["align-scribe-receipt", .. CoverWorld.AlignArgs(inputs)],
            CoverWorld.Environment(temporary.Path, directoryInputs, directoryInputs.Files),
            console);

        Assert.Equal(0, exitCode);
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
    public void AlignRepairsScribeReceiptWhilePreservingCoverageMismatchDiagnostic()
    {
        var inputs = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec());
        var entry = Assert.Single(
            inputs.Document.RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        var oldCoverage = Assert.Single(entry.Receipts.Coverage);
        var source = Assert.Single(inputs.Document.RequireDigestionSources());
        var driftedDocument = inputs.Document.WithDigestionSources(
        [
            source with
            {
                Entries = source.Entries.Select(candidate => candidate.AtomId == entry.AtomId
                    ? candidate with
                    {
                        Receipts = candidate.Receipts with
                        {
                            Coverage =
                            [
                                oldCoverage with
                                {
                                    TargetSha256 = "sha256:" + new string('c', 64),
                                },
                            ],
                        },
                    }
                    : candidate).ToImmutableArray(),
            },
        ]);
        var driftedFiles = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(driftedFiles, driftedDocument);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, driftedFiles);
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["align-scribe-receipt", .. CoverWorld.AlignArgs(inputs)],
            CoverWorld.Environment(temporary.Path, inputs, driftedFiles),
            console);

        Assert.True(exitCode == 0, $"exit_code={exitCode} stderr={console.Error}");
        Assert.Equal(string.Empty, console.Error);
        Assert.Contains("ledger_changed=true", console.Output, StringComparison.Ordinal);
        var alignedLedger = DirectoryLedgerTestSupport.Image(
            BackfillInventoryLoader.LoadRoot(temporary.Path));
        Assert.NotEqual(
            DirectoryLedgerTestSupport.Image(driftedDocument),
            alignedLedger);
        var alignedFiles = FilesWithLedgerFromRoot(driftedFiles, temporary.Path);
        var status = CoverWorld.Environment(temporary.Path, inputs, alignedFiles)
            .DigestStatus(Array.Empty<string>());
        Assert.False(status.Success);
        Assert.Contains("coverage-receipt-mismatch", status.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("scribe-definition-mismatch", status.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("scribe-emission-mismatch", status.Error, StringComparison.Ordinal);
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
    public void CoverAtomLeavesLedgerBytesUnchangedWhenAGateRejects()
    {
        var inputs = CoverWorld.Materialize(new CoverSpec { VerifyScribe = false });
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, inputs.Ledger, new UTF8Encoding(false));
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.CoverAtom(CoverArgs(inputs));

        Assert.False(result.Success);
        Assert.Contains("COVER_INVALID", result.Error, StringComparison.Ordinal);
        Assert.Equal(inputs.Ledger, File.ReadAllText(outputPath));
    }

    [Fact]
    public void CoverAtomReplayIsByteIdenticalAndSecondRunIsRejected()
    {
        var inputs = DirectoryInputs(CoverWorld.Materialize(new CoverSpec()));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var before = DirectoryLedgerImage(temporary.Path);

        var first = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files)
            .CoverAtom(CoverArgs(inputs));

        Assert.True(first.Success, first.Error);
        var afterFirst = DirectoryLedgerImage(temporary.Path);
        Assert.NotEqual(before, afterFirst);

        var replayFiles = FilesWithLedgerFromRoot(inputs.Files, temporary.Path);
        var second = BuildCoverEnvironment(temporary.Path, inputs, replayFiles)
            .CoverAtom(CoverArgs(inputs));

        Assert.False(second.Success);
        Assert.Contains("already has coverage", second.Error, StringComparison.Ordinal);
        Assert.Equal(afterFirst, DirectoryLedgerImage(temporary.Path));
    }

    private static CoverInputs DirectoryInputs(CoverInputs inputs) => inputs with
    {
        Files = DirectoryLedgerTestSupport.Project(inputs.Files),
        Baseline = DirectoryLedgerTestSupport.Project(inputs.Baseline),
    };

    private static Dictionary<string, string> FilesWithLedgerFromRoot(
        IReadOnlyDictionary<string, string> files,
        string repositoryRoot)
    {
        var result = new Dictionary<string, string>(files, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(
            result,
            BackfillInventoryLoader.LoadRoot(repositoryRoot));
        return result;
    }

    private static string DirectoryLedgerImage(string repositoryRoot)
    {
        var root = Path.GetFullPath(repositoryRoot);
        var paths = Directory.EnumerateFiles(
                Path.Combine(root, BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar)),
                "*",
                SearchOption.AllDirectories)
            .Order(StringComparer.Ordinal);
        return string.Concat(paths.Select(path =>
            Path.GetRelativePath(root, path).Replace(Path.DirectorySeparatorChar, '/')
            + "\0"
            + Convert.ToBase64String(File.ReadAllBytes(path))
            + "\n"));
    }

    private static ProductionCliEnvironment BuildCoverEnvironment(
        string repositoryRoot,
        CoverInputs inputs,
        IReadOnlyDictionary<string, string> currentFiles) =>
        new(
            repositoryRoot,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(currentFiles),
                CoverWorld.Raw(inputs.Baseline)),
            new FakeLeanReportSource(inputs.Report),
            new FakeScribeEmissionVerifier(inputs.VerifiedEmissions));

    private static string[] CoverArgs(CoverInputs inputs) =>
        ["--cover-atom", CoverWorld.DefaultAtomId, "--gid", inputs.Gid, "--base", "baseline",
            "--envelope", inputs.EnvelopePath];
}
