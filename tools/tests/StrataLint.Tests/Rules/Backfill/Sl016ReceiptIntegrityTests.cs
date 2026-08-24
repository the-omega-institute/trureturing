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
    public void ReceiptIntegrityDeltaAllowsRepairAndBlocksNewOrWorsenedIdentity()
    {
        var clean = ReceiptEvaluation();
        var existing = ReceiptEvaluation("gid-a");
        var worsened = ReceiptEvaluation("gid-b");

        Assert.Empty(DigestionReceiptIntegrity.NewFailureReasons(existing, clean));
        Assert.Equal(
            "atom-a:coverage-receipt-mismatch:gid-a",
            Assert.Single(DigestionReceiptIntegrity.NewFailureReasons(clean, existing)));
        Assert.Equal(
            "atom-a:coverage-receipt-mismatch:gid-b",
            Assert.Single(DigestionReceiptIntegrity.NewFailureReasons(existing, worsened)));
    }

    [Theory]
    [InlineData("coverage-receipt-missing")]
    [InlineData("scribe-receipt-missing")]
    [InlineData("scribe-emission-unverified")]
    public void LegalMissingAndUnverifiedGapsRemainNonFatal(string code)
    {
        Assert.Equal(DigestionGapSeverity.NonFatal, new DigestionGap(code, "gid-a").Severity);
    }

    [Fact]
    public void AllLedgerWritersConsumePlannedReceiptIntegrityDeltaBeforeWritingBytes()
    {
        var writers = new[]
        {
            (Path: "tools/StrataLint.Cli/Commands/Digestion/CoverAtomCommand.cs",
                Source: TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
                    "tools/StrataLint.Cli/Commands/Digestion/CoverAtomCommand.cs")),
                WriteCall: "IngestCommand.ApplyLedgerUpdatesAtomically("),
            (Path: "tools/StrataLint.Cli/Commands/Digestion/IngestCommand.cs",
                Source: TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
                    "tools/StrataLint.Cli/Commands/Digestion/IngestCommand.cs")),
                WriteCall: "WriteCasObjects("),
            (Path: "tools/StrataLint.Cli/Commands/Digestion/CoverAtomCommand.AlignScribe.cs",
                Source: TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
                    "tools/StrataLint.Cli/Commands/Digestion/CoverAtomCommand.AlignScribe.cs")),
                WriteCall: "IngestCommand.ApplyLedgerUpdatesAtomically("),
        };

        foreach (var writer in writers)
        {
            var guard = writer.Source.IndexOf(
                "DigestionReceiptIntegrityGuard.RequireNoNewFailures(",
                StringComparison.Ordinal);
            var write = writer.Source.IndexOf(writer.WriteCall, StringComparison.Ordinal);
            Assert.True(guard >= 0, $"{writer.Path} is missing its planned-state receipt guard");
            Assert.True(write > guard, $"{writer.Path} consumes its planned-state guard after writing");
        }
    }

    [Fact]
    public void CliReceiptIntegrityConsumersContainNoPrivateFatalCodeFork()
    {
        var consumers = new[]
        {
            TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
                "tools/StrataLint.Cli/Commands/DigestStatusCommand.cs")),
            TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
                "tools/StrataLint.Cli/Commands/Digestion/CoverAtomCommand.cs")),
            TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
                "tools/StrataLint.Cli/Commands/Digestion/CoverAtomCommand.AlignScribe.cs")),
            TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
                "tools/StrataLint.Cli/Commands/Digestion/DigestionReceiptIntegrityGuard.cs")),
            TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
                "tools/StrataLint.Cli/Commands/Digestion/IngestCommand.cs")),
            TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
                "tools/StrataLint.Cli/Commands/TheoryGeneration/TheoryCandidatesCommand.cs")),
            TestRepositoryLayout.ReadAllText(RepositoryRelativePath.Create(
                "tools/StrataLint.Cli/Commands/TruthRelease/ResidualFrontierAssembler.cs")),
        };
        var offenders = consumers
            .Where(source => FatalCodes.Any(code => source.Contains(code, StringComparison.Ordinal)))
            .ToArray();

        Assert.Empty(offenders);
    }

    private static readonly string[] FatalCodes =
    [
        "coverage-receipt-mismatch",
        "scribe-definition-mismatch",
        "scribe-emission-mismatch",
    ];

    private static DigestionLedgerEvaluation ReceiptEvaluation(string? detail = null)
    {
        var status = new DigestionStatus(
            DigestionMigrationState.Partial,
            DigestionTruthState.Closed);
        var entry = new DigestionLedgerEntry(
            "source-a",
            "synthetic.md",
            "synthetic-v1",
            "atom-a",
            "synthetic/path",
            null,
            new DigestionFingerprints("sha256:synthetic", "sha256:synthetic"),
            [],
            new DigestionReceipts([], [], [], [], null),
            status,
            "sha256:synthetic");
        return new DigestionLedgerEvaluation(
            [
                new DigestionEntryEvaluation(
                    entry,
                    DigestionReceiptAlignment.Seen,
                    status,
                    false,
                    detail is null
                        ? []
                        : [new DigestionGap("coverage-receipt-mismatch", detail)]),
            ],
            []);
    }

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
