using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CoverAtomTests
{
    [Fact]
    public void CoverCanStartWhenFreshLaneHeadEqualsReceiptOwningBase()
    {
        var inputs = new CoverSpec { EnvelopeInBaseline = true }.Materialize();
        var current = CoverWorld.Raw(inputs.Files);
        using var temporary = new TemporaryDirectory();
        var outputPath = Path.Combine(temporary.Path, BackfillInventoryLoader.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
        File.WriteAllText(outputPath, inputs.Ledger, new UTF8Encoding(false));
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                current,
                current),
            new FakeLeanReportSource(inputs.Report),
            new FakeScribeEmissionVerifier(inputs.VerifiedEmissions));

        var result = environment.CoverAtom(
            ["--cover-atom", CoverWorld.DefaultAtomId,
                "--gid", inputs.Gid,
                "--base", "HEAD",
                "--envelope", inputs.EnvelopePath]);

        Assert.True(result.Success, result.Error);
        Assert.NotEqual(inputs.Ledger, File.ReadAllText(outputPath));
    }

    [Fact]
    public void AdmissionRejectsCoverageBackedOnlyByCandidateReceipt()
    {
        var spec = new CoverSpec { EnvelopeInBaseline = true };
        var (cover, coveredLedger, _) = Execute(spec);
        Assert.True(cover.Success, cover.Error);
        var inputs = spec.Materialize();
        inputs.Files[BackfillInventoryLoader.RelativePath] = coveredLedger;
        inputs.Baseline.Remove(inputs.EnvelopePath);
        var current = DecodeSnapshot(inputs.Files);
        var forkPoint = DecodeSnapshot(inputs.Baseline);
        var policy = Assert.IsType<RegistryLoadOutcome.Accepted>(RegistryLoader.Load(
            Encoding.UTF8.GetBytes(TestRegistry.Canonical),
            Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(current, inputs.Report)).Capability;

        var findings = BackfillInventoryRule.EvaluateDocument(
            new BackfillInventoryValidationContext(
                current,
                forkPoint,
                policy,
                lean,
                inputs.VerifiedEmissions),
            BackfillInventoryLoader.Load(current));

        Assert.Contains(findings, finding => finding.Message.Contains(
            "base-owned formalization receipt",
            StringComparison.Ordinal));
    }

    [Fact]
    public void AdmissionRejectsReplacingPrimaryCoverageWithHostedExtension()
    {
        const string primary = "D5/S0/Carrier/Probe.probe";
        const string hostedModule = "D5/S3/Observer/WindowRegisterCRT";
        const string hostedDeclaration = "window_register_crt_decomposition";
        const string hosted = hostedModule + "." + hostedDeclaration;
        var spec = new CoverSpec
        {
            InitialCoverage = [primary],
            SecondaryTarget = (hostedModule, hostedDeclaration),
        };
        var inputs = spec.Materialize();
        var baseline = DecodeSnapshot(inputs.Baseline);
        var currentText = inputs.Ledger.Replace(
            $"        coverage_gids:\n          - {primary}\n",
            $"        coverage_gids:\n          - {hosted}\n",
            StringComparison.Ordinal);
        Assert.NotEqual(inputs.Ledger, currentText);
        inputs.Files[BackfillInventoryLoader.RelativePath] = currentText;
        var current = DecodeSnapshot(inputs.Files);
        var policy = Assert.IsType<RegistryLoadOutcome.Accepted>(RegistryLoader.Load(
            Encoding.UTF8.GetBytes(TestRegistry.Canonical),
            Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(current, inputs.Report)).Capability;

        var findings = BackfillInventoryRule.EvaluateDocument(
            new BackfillInventoryValidationContext(
                current,
                baseline,
                policy,
                lean,
                inputs.VerifiedEmissions),
            BackfillInventoryLoader.Load(current));

        Assert.Contains(findings, finding => finding.Message.Contains(
            "absent from current coverage",
            StringComparison.Ordinal));
    }

    [Fact]
    public void AdmissionRejectsCrossAtomCoverageWithoutForkPointSharedResidualHost()
    {
        var spec = new CoverSpec
        {
            OtherAtomBinding = ("candidate-only-sibling", "D5/S0/Carrier/Probe.probe"),
        };
        var inputs = spec.Materialize();
        var (cover, coveredLedger, _) = Execute(spec);
        Assert.False(cover.Success);
        inputs.Files[BackfillInventoryLoader.RelativePath] = coveredLedger;
        var currentText = inputs.Ledger.Replace(
            "        coverage_gids: []\n",
            "        coverage_gids:\n          - D5/S0/Carrier/Probe.probe\n",
            StringComparison.Ordinal);
        Assert.NotEqual(inputs.Ledger, currentText);
        inputs.Files[BackfillInventoryLoader.RelativePath] = currentText;
        var current = DecodeSnapshot(inputs.Files);
        var baseline = DecodeSnapshot(inputs.Baseline);
        var policy = Assert.IsType<RegistryLoadOutcome.Accepted>(RegistryLoader.Load(
            Encoding.UTF8.GetBytes(TestRegistry.Canonical),
            Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(current, inputs.Report)).Capability;

        var findings = BackfillInventoryRule.EvaluateDocument(
            new BackfillInventoryValidationContext(
                current,
                baseline,
                policy,
                lean,
                inputs.VerifiedEmissions),
            BackfillInventoryLoader.Load(current));

        Assert.Contains(findings, finding => finding.Message.Contains(
            "different residual paths",
            StringComparison.Ordinal));
    }

    private static RepositorySnapshot DecodeSnapshot(IReadOnlyDictionary<string, string> files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(CoverWorld.Raw(files))).Snapshot;
}
