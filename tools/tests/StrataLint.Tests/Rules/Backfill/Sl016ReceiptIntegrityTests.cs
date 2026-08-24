using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class Sl016ReceiptIntegrityTests
{
    [Theory]
    [InlineData("coverage-receipt-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void NewReceiptIntegrityIdentityBlocksSl016Admission(string mismatchCode)
    {
        var evaluation = EvaluateReceiptIntegrityGap(
            mismatchCode,
            gapExistsInBaseline: false,
            forceFullScan: false);

        var diagnostic = Assert.Single(evaluation.Diagnostics, item => item.Message.Contains(
            mismatchCode,
            StringComparison.Ordinal));
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
    }

    [Theory]
    [InlineData("coverage-receipt-mismatch")]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void ExistingReceiptIntegrityIdentityIsObservedDuringSl016FullScan(string mismatchCode)
    {
        var evaluation = EvaluateReceiptIntegrityGap(
            mismatchCode,
            gapExistsInBaseline: true,
            forceFullScan: true);

        var diagnostic = Assert.Single(evaluation.Diagnostics, item => item.Message.Contains(
            mismatchCode,
            StringComparison.Ordinal));
        Assert.Equal(AdmissionEffect.Observe, diagnostic.AdmissionEffect);
        Assert.DoesNotContain(evaluation.Diagnostics, static item =>
            item.AdmissionEffect == AdmissionEffect.Block);
    }

    [Fact]
    public void ReceiptIntegrityGapIdentityEqualityUsesAtomIdCodeAndDetail()
    {
        var identityType = typeof(DigestionGap).Assembly.GetType(
            "StrataLint.Engine.DigestionReceiptIntegrityGapIdentity");
        Assert.NotNull(identityType);
        var constructor = Assert.Single(identityType.GetConstructors());
        object Identity(string atomId, string code, string detail) =>
            constructor.Invoke([atomId, code, detail]);
        var reference = Identity("atom-a", "coverage-receipt-mismatch", "gid-a");

        Assert.NotEqual(reference, Identity("atom-b", "coverage-receipt-mismatch", "gid-a"));
        Assert.NotEqual(reference, Identity("atom-a", "scribe-definition-mismatch", "gid-a"));
        Assert.NotEqual(reference, Identity("atom-a", "coverage-receipt-mismatch", "gid-b"));
    }

    [Fact]
    public void CliReceiptIntegrityConsumersContainNoPrivateFatalCodeFork()
    {
        var root = TestRepositoryLayout.FindRoot();
        var commandRoot = Path.Combine(root, "tools", "StrataLint.Cli", "Commands");
        var offenders = Directory.EnumerateFiles(commandRoot, "*.cs", SearchOption.AllDirectories)
            .Select(path => (Path: path, Text: File.ReadAllText(path)))
            .Where(file => FatalCodes.Any(code => file.Text.Contains(code, StringComparison.Ordinal)))
            .Select(file => Path.GetRelativePath(root, file.Path).Replace(Path.DirectorySeparatorChar, '/'))
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Empty(offenders);
    }

    private static readonly string[] FatalCodes =
    [
        "coverage-receipt-mismatch",
        "scribe-definition-mismatch",
        "scribe-emission-mismatch",
    ];

    private static SingleRuleEvaluation EvaluateReceiptIntegrityGap(
        string mismatchCode,
        bool gapExistsInBaseline,
        bool forceFullScan)
    {
        const string atomPath =
            "Meta/Digestion/backfill/delta-v0.1/partial-closed/delta-atom.yaml";
        const string coverageGid = "D5/S0/Carrier/BackfillTarget";
        const string targetPath = coverageGid + ".lean";
        const string definition = "fixture Scribe definition\n";
        const string emission = "# Fixture Scribe emission\n";
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.UseValidDirectoryBackfill();
        var definitionPath = ScribeEmissionAttestation.DefinitionPath(coverageGid);
        var emissionPath = ScribeEmissionAttestation.EmissionPath(coverageGid);
        var definitionSha256 = Sha256(definition);
        var emissionSha256 = Sha256(emission);
        var targetSha256 = Sha256(fixture.Files[targetPath]);
        var mismatchSha256 = "sha256:" + new string('0', 64);
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[targetPath] = fixture.Files[targetPath];
            files[definitionPath] = definition;
            files[emissionPath] = emission;
        }

        var receiptProjection = "coverage:\n"
            + $"    - gid: {coverageGid}\n"
            + $"      source_sha256: {RuleFixture.FixtureCasReference}\n"
            + $"      target_sha256: {(mismatchCode == "coverage-receipt-mismatch" ? mismatchSha256 : targetSha256)}\n"
            + "  scribe:\n"
            + $"    - gid: {coverageGid}\n"
            + $"      definition_sha256: {(mismatchCode == "scribe-definition-mismatch" ? mismatchSha256 : definitionSha256)}\n"
            + $"      emission_sha256: {(mismatchCode == "scribe-emission-mismatch" ? mismatchSha256 : emissionSha256)}";
        fixture.Files[atomPath] = AddReceipts(fixture.Files[atomPath], receiptProjection);
        if (gapExistsInBaseline)
        {
            fixture.Baseline[atomPath] = AddReceipts(fixture.Baseline[atomPath], receiptProjection);
            fixture.ForkPoint[atomPath] = AddReceipts(fixture.ForkPoint[atomPath], receiptProjection);
        }

        var verified = VerifiedScribeEmissions.Create(
        [
            new ScribeEmissionRecord(
                coverageGid,
                definitionPath,
                definitionSha256,
                emissionPath,
                emissionSha256),
        ]);
        var changedPaths = forceFullScan
            ? new[] { "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs" }
            : new[] { atomPath };
        var context = fixture.Build(
            RawChangeSet.Create(changedPaths),
            verifiedScribeEmissions: verified);
        return RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), context);
    }

    private static string AddReceipts(string atom, string receiptProjection) => atom.Replace(
        "coverage: []\n  scribe: []",
        receiptProjection,
        StringComparison.Ordinal);

    private static string Sha256(string text) =>
        DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(text)).RawSha256;
}
