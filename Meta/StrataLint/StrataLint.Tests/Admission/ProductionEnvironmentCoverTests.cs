using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void AlignScribeReceiptIsReachableThroughProductionCliDispatch()
    {
        var inputs = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec());
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, inputs.Ledger, new UTF8Encoding(false));
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["align-scribe-receipt", .. CoverWorld.AlignArgs(inputs)],
            CoverWorld.Environment(temporary.Path, inputs, inputs.Files),
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
        var inputs = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec());
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, inputs.Ledger, new UTF8Encoding(false));
        var initialEnvironment = CoverWorld.Environment(temporary.Path, inputs, inputs.Files);

        var before = initialEnvironment.DigestStatus(Array.Empty<string>());
        Assert.False(before.Success);
        Assert.Contains("scribe-definition-mismatch", before.Error, StringComparison.Ordinal);
        Assert.Contains("scribe-emission-mismatch", before.Error, StringComparison.Ordinal);

        var aligned = initialEnvironment.AlignScribeReceipt(CoverWorld.AlignArgs(inputs));
        Assert.True(aligned.Success, aligned.Error);
        var alignedLedger = File.ReadAllText(outputPath);
        var alignedFiles = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal)
        {
            [BackfillInventoryLoader.RelativePath] = alignedLedger,
        };
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
            BackfillInventoryLoader.Load(inputs.Ledger).RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        var oldCoverage = Assert.Single(entry.Receipts.Coverage);
        var driftedLedger = inputs.Ledger.Replace(
            oldCoverage.TargetSha256,
            "sha256:" + new string('c', 64),
            StringComparison.Ordinal);
        var driftedFiles = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal)
        {
            [BackfillInventoryLoader.RelativePath] = driftedLedger,
        };
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, driftedLedger, new UTF8Encoding(false));
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["align-scribe-receipt", .. CoverWorld.AlignArgs(inputs)],
            CoverWorld.Environment(temporary.Path, inputs, driftedFiles),
            console);

        Assert.True(exitCode == 0, $"exit_code={exitCode} stderr={console.Error}");
        Assert.Equal(string.Empty, console.Error);
        Assert.Contains("ledger_changed=true", console.Output, StringComparison.Ordinal);
        var alignedLedger = File.ReadAllText(outputPath);
        Assert.NotEqual(driftedLedger, alignedLedger);
        var alignedFiles = new Dictionary<string, string>(driftedFiles, StringComparer.Ordinal)
        {
            [BackfillInventoryLoader.RelativePath] = alignedLedger,
        };
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
        Assert.True(inputs.VerifiedEmissions!.TryGet(
            inputs.Gid[..inputs.Gid.LastIndexOf('.')], out var verifiedRecord));
        var inconsistentVerification = VerifiedScribeEmissions.Create(
            [verifiedRecord with { DefinitionSha256 = "sha256:" + new string('c', 64) }],
            [inputs.Gid]);
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, inputs.Ledger, new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                CoverWorld.Raw(inputs.Files),
                CoverWorld.Raw(inputs.Baseline)),
            new FakeLeanReportSource(inputs.Report),
            new FakeScribeEmissionVerifier(inconsistentVerification));

        var result = environment.AlignScribeReceipt(CoverWorld.AlignArgs(inputs));

        Assert.False(result.Success);
        Assert.Contains("scribe-definition-mismatch", result.Error, StringComparison.Ordinal);
        Assert.Equal(inputs.Ledger, File.ReadAllText(outputPath));
    }

    [Fact]
    public void CoverAtomWritesCoverageAndRecomputesDigestStatusThroughProductionEnvironment()
    {
        var inputs = CoverWorld.Materialize(new CoverSpec());
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, inputs.Ledger, new UTF8Encoding(false));
        var environment = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files);

        var result = environment.CoverAtom(CoverArgs(inputs));

        Assert.True(result.Success, result.Error);
        Assert.Contains("ledger_changed=true", result.Output, StringComparison.Ordinal);
        Assert.Contains("DIGEST_STATUS", result.Output, StringComparison.Ordinal);
        var written = File.ReadAllText(outputPath);
        Assert.NotEqual(inputs.Ledger, written);
        var entry = Assert.Single(
            BackfillInventoryLoader.Load(written).RequireDigestionEntries(),
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
        var inputs = CoverWorld.Materialize(new CoverSpec());
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, inputs.Ledger, new UTF8Encoding(false));

        var first = BuildCoverEnvironment(temporary.Path, inputs, inputs.Files)
            .CoverAtom(CoverArgs(inputs));

        Assert.True(first.Success, first.Error);
        var afterFirst = File.ReadAllText(outputPath);
        Assert.NotEqual(inputs.Ledger, afterFirst);

        var replayFiles = new Dictionary<string, string>(inputs.Files, StringComparer.Ordinal)
        {
            [BackfillInventoryLoader.RelativePath] = afterFirst,
        };
        var second = BuildCoverEnvironment(temporary.Path, inputs, replayFiles)
            .CoverAtom(CoverArgs(inputs));

        Assert.False(second.Success);
        Assert.Contains("already has coverage", second.Error, StringComparison.Ordinal);
        Assert.Equal(afterFirst, File.ReadAllText(outputPath));
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
