using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void CoverAtomAlignModeIsReachableThroughCliDispatch()
    {
        var inputs = CoverWorld.Materialize(CoverWorld.StaleReceiptSpec());
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, inputs.Ledger, new UTF8Encoding(false));
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["cover-atom", .. CoverWorld.AlignArgs(inputs)],
            CoverWorld.Environment(temporary.Path, inputs, inputs.Files),
            console);

        Assert.Equal(0, exitCode);
        Assert.Contains("ALIGN_SCRIBE_RECEIPT", console.Output, StringComparison.Ordinal);
        Assert.Equal(string.Empty, console.Error);
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

        var aligned = initialEnvironment.CoverAtom(CoverWorld.AlignArgs(inputs));
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
