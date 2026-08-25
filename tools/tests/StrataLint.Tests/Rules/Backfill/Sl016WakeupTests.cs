using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

// SL-016 的唤醒路径。独立成文件而非并入 RuleEngineTests:后者已达 SL-003 硬线 800 行,
// 按 CLAUDE.md 第 8 条「桶满则裂、只裂不迁」,新条目入新桶,既有条目原地不动。
public sealed class Sl016WakeupTests
{
    // 理论卷改按路径规则治理后,GovernanceDocuments 里已无理论路径。若 IsAffectedBy
    // 仍只靠那张清单,只改理论卷的候选就**整条规则不触发**(RuleCatalog 对未命中的
    // 规则整条跳过),消化账本检测随之失效——实测见 #2462:追加一条可原子化命题、
    // 不跑 make ingest,make gate EXIT=0 放行。此测试钉住该唤醒路径。
    [Fact]
    public void TheoryVolumeChangeWakesSl016EvenThoughItIsNoLongerEnumeratedInTheRegistry()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create(
            ["docs/develop/theory/INTERFACE_PAPER.md"]));

        Assert.DoesNotContain(
            context.Policy.GovernanceDocuments,
            static path => path.Value.StartsWith(
                DigestionOpaquePathPolicy.TheoryRootPath,
                StringComparison.Ordinal));
        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
    }

    // IsOpaque 名出三类输入,其改动都能移动原子投影。理论那一类由上面钉住;CAS 那一类
    // 此前无钉子,而「唯一析取项静默失配」正是本文件刚发生过的事故(#2459 清空
    // governance_documents 后,理论卷那一路无声失效)。同形状,同钉法。
    //
    // 第三类 `Meta/Digestion/atomizers.toml` **不在此处钉**:它同时被 governance_documents
    // 命中,故删掉 IsAffectedBy 里那条专用析取项也不会让任何测试变红(已实测)。
    // 那条析取项因此是双保险而非死代码——一旦该文件像理论卷那样被移出清单,它就是
    // 唯一的退路。要钉住它需要一份不含该条目的 registry 夹具,另行处理,不在此假装已钉。
    [Fact]
    public void ContentAddressedAtomChangeWakesSl016()
    {
        const string path =
            "Meta/Digestion/atoms/sha256/0000000000000000000000000000000000000000000000000000000000000000";
        Assert.True(
            DigestionOpaquePathPolicy.IsOpaque(RepoPath.CreateKnown(path)),
            $"{path} is expected to be an opaque digestion input");

        var fixture = new RuleFixture();

        Assert.True(BackfillInventoryRule.IsAffectedBy(fixture.Build(RawChangeSet.Create([path]))));
    }

    [Fact]
    public void UnchangedBaseEntryDuplicateCoverageIsNotRepublishedForUnrelatedDelta()
    {
        var fixture = new RuleFixture();
        fixture.UseValidDirectoryBackfill();
        const string atomPath =
            "Meta/Digestion/backfill/delta-v0.1/partial-closed/delta-atom.yaml";
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[atomPath] = files[atomPath].Replace(
                "coverage_gids:\n  - D5/S0/Carrier/BackfillTarget",
                "coverage_gids:\n  - D5/S0/Carrier/BackfillTarget\n  - D5/S0/Carrier/BackfillTarget",
                StringComparison.Ordinal);
        }

        var findings = BackfillInventoryRule.EvaluateCandidateDelta(
            fixture.Build(RawChangeSet.Create(["D5/S3/Probe/Unrelated.lean"])));

        Assert.DoesNotContain(findings, finding => finding.Message.Contains(
            "duplicate coverage GIDs",
            StringComparison.Ordinal));
    }

    [Fact]
    public void ChangedEntryDuplicateCoverageStillProducesFinding()
    {
        var fixture = new RuleFixture();
        fixture.UseValidDirectoryBackfill();
        const string atomPath =
            "Meta/Digestion/backfill/delta-v0.1/partial-closed/delta-atom.yaml";
        fixture.Files[atomPath] = fixture.Files[atomPath].Replace(
            "coverage_gids:\n  - D5/S0/Carrier/BackfillTarget",
            "coverage_gids:\n  - D5/S0/Carrier/BackfillTarget\n  - D5/S0/Carrier/BackfillTarget",
            StringComparison.Ordinal);

        var findings = BackfillInventoryRule.EvaluateCandidateDelta(
            fixture.Build(RawChangeSet.Create([atomPath])));

        Assert.Contains(findings, finding => finding.Message.Contains(
            "duplicate coverage GIDs",
            StringComparison.Ordinal));
    }

    [Fact]
    public void UnchangedBaseSourceMetadataIsNotStrictlyReparsedForUnrelatedDelta()
    {
        var fixture = new RuleFixture();
        fixture.UseValidDirectoryBackfill();
        const string sourcePath =
            "Meta/Digestion/backfill/delta-v0.1/source.toml";
        fixture.Files[sourcePath] += "\n";

        var findings = BackfillInventoryRule.EvaluateCandidateDelta(
            fixture.Build(RawChangeSet.Create(["D5/S3/Probe/Unrelated.lean"])));

        Assert.DoesNotContain(findings, finding => finding.Message.Contains(
            "source metadata",
            StringComparison.Ordinal));
    }

    [Fact]
    public void ChangedSourceMetadataStillUsesStrictCanonicalEncoding()
    {
        var fixture = new RuleFixture();
        fixture.UseValidDirectoryBackfill();
        const string sourcePath =
            "Meta/Digestion/backfill/delta-v0.1/source.toml";
        fixture.Files[sourcePath] += "\n";

        var findings = BackfillInventoryRule.EvaluateCandidateDelta(
            fixture.Build(RawChangeSet.Create([sourcePath])));

        Assert.Contains(findings, finding => finding.Message.Contains(
            "source metadata",
            StringComparison.Ordinal));
    }

    [Fact]
    public void CandidateBackfillPairWithoutBaselineFormalizationPrecommitIsBlocked()
    {
        const string atomPath =
            "Meta/Digestion/backfill/delta-v0.1/partial-closed/delta-atom.yaml";
        const string gid = "D5/S0/Carrier/BackfillTarget.protectedTargetFixture";
        var (fixture, verifiedScribeEmissions, receiptProjection) =
            PreparedDeclarationPairFixture(gid);
        fixture.Files[atomPath] = AddCoverageAndReceipts(
            fixture.Files[atomPath],
            gid,
            receiptProjection);

        var evaluation = EvaluateSl016(
            fixture,
            verifiedScribeEmissions,
            [atomPath]);

        Assert.Contains(evaluation.Diagnostics, finding =>
            finding.AdmissionEffect == AdmissionEffect.Block
            && finding.Message.Contains(gid, StringComparison.Ordinal)
            && finding.Message.Contains(
                "base-owned formalization precommitment",
                StringComparison.Ordinal));
    }

    [Fact]
    public void CandidateCannotReuseGidOnSecondAtomWithoutThatAtomsPrecommitment()
    {
        const string firstAtomPath =
            "Meta/Digestion/backfill/delta-v0.1/partial-closed/delta-atom.yaml";
        const string secondAtomPath =
            "Meta/Digestion/backfill/delta-v0.1/partial-closed/second-atom.yaml";
        const string gid = "D5/S0/Carrier/BackfillTarget.protectedTargetFixture";
        var (fixture, verifiedScribeEmissions, receiptProjection) =
            PreparedDeclarationPairFixture(gid);
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[firstAtomPath] = AddCoverageAndReceipts(
                files[firstAtomPath],
                gid,
                receiptProjection);
        }

        AddFormalizationPrecommitment(fixture, "delta-atom", gid);
        fixture.Files[secondAtomPath] = fixture.Files[firstAtomPath].Replace(
            "ast_path: manual/fixture",
            "ast_path: manual/second-fixture",
            StringComparison.Ordinal);

        var evaluation = EvaluateSl016(
            fixture,
            verifiedScribeEmissions,
            [secondAtomPath]);

        Assert.Contains(evaluation.Diagnostics, finding =>
            finding.AdmissionEffect == AdmissionEffect.Block
            && finding.Message.Contains("second-atom", StringComparison.Ordinal)
            && finding.Message.Contains(gid, StringComparison.Ordinal)
            && finding.Message.Contains(
                "base-owned formalization precommitment",
                StringComparison.Ordinal));
    }

    [Fact]
    public void ExistingCoveragePairReboundToNewRawFingerprintRequiresNewPrecommitment()
    {
        const string atomPath =
            "Meta/Digestion/backfill/delta-v0.1/partial-closed/delta-atom.yaml";
        const string gid = "D5/S0/Carrier/BackfillTarget.protectedTargetFixture";
        var (fixture, _, receiptProjection) = PreparedDeclarationPairFixture(gid);
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[atomPath] = AddCoverageAndReceipts(files[atomPath], gid, receiptProjection);
        }
        AddFormalizationPrecommitment(fixture, "delta-atom", gid);
        var reboundFingerprint = "sha256:" + new string('9', 64);
        fixture.Files[atomPath] = fixture.Files[atomPath].Replace(
            RuleFixture.FixtureCasReference,
            reboundFingerprint,
            StringComparison.Ordinal);
        var context = fixture.Build(RawChangeSet.Create([atomPath]));

        var findings = DigestionFormalizationPrecommitmentValidator.ValidateNewEdges(
            BackfillInventoryLoader.LoadBaseline(context.Baseline),
            BackfillInventoryLoader.Load(context.Current),
            context.Baseline,
            context.Lean.Report);

        Assert.Contains(findings, finding =>
            finding.Contains(gid, StringComparison.Ordinal)
            && finding.Contains("formalization receipt fingerprint does not match atom", StringComparison.Ordinal));
    }

    [Fact]
    public void ExistingCoveragePairReceiptRebindingCannotReuseEntryFingerprintExemption()
    {
        const string atomPath =
            "Meta/Digestion/backfill/delta-v0.1/partial-closed/delta-atom.yaml";
        const string gid = "D5/S0/Carrier/BackfillTarget.protectedTargetFixture";
        var (fixture, _, receiptProjection) = PreparedDeclarationPairFixture(gid);
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[atomPath] = AddCoverageAndReceipts(files[atomPath], gid, receiptProjection);
        }

        var reboundFingerprint = "sha256:" + new string('9', 64);
        fixture.Files[atomPath] = fixture.Files[atomPath].Replace(
            $"source_sha256: {RuleFixture.FixtureCasReference}",
            $"source_sha256: {reboundFingerprint}",
            StringComparison.Ordinal);
        var context = fixture.Build(RawChangeSet.Create([atomPath]));

        var findings = DigestionFormalizationPrecommitmentValidator.ValidateNewEdges(
            BackfillInventoryLoader.LoadBaseline(context.Baseline),
            BackfillInventoryLoader.Load(context.Current),
            context.Baseline,
            context.Lean.Report);

        Assert.Contains(findings, finding =>
            finding.Contains(gid, StringComparison.Ordinal)
            && finding.Contains("base-owned formalization precommitment", StringComparison.Ordinal));
    }

    [Fact]
    public void ExistingCoveragePairWithSameRawFingerprintKeepsItsExemption()
    {
        const string atomPath =
            "Meta/Digestion/backfill/delta-v0.1/partial-closed/delta-atom.yaml";
        const string gid = "D5/S0/Carrier/BackfillTarget.protectedTargetFixture";
        var (fixture, _, receiptProjection) = PreparedDeclarationPairFixture(gid);
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[atomPath] = AddCoverageAndReceipts(files[atomPath], gid, receiptProjection);
        }
        var context = fixture.Build(RawChangeSet.Create([atomPath]));

        var findings = DigestionFormalizationPrecommitmentValidator.ValidateNewEdges(
            BackfillInventoryLoader.LoadBaseline(context.Baseline),
            BackfillInventoryLoader.Load(context.Current),
            context.Baseline,
            context.Lean.Report);

        Assert.Empty(findings);
    }

    [Fact]
    public void ExistingComparableReceiptIntegrityGapProducesNoBlockDuringSl016FullScan()
    {
        var (context, evaluation) = EvaluateReceiptIntegrityGap(
            "coverage-receipt-mismatch",
            gapExistsInBaseline: true);

        var diagnostic = Assert.Single(evaluation.Diagnostics, item => item.Message.Contains(
            "coverage-receipt-mismatch",
            StringComparison.Ordinal));
        Assert.True(context.RuleImplementationChanged);
        Assert.Equal(AdmissionEffect.Observe, diagnostic.AdmissionEffect);
        Assert.DoesNotContain(evaluation.Diagnostics, item =>
            item.AdmissionEffect == AdmissionEffect.Block);
    }

    [Fact]
    public void ReceiptIntegrityGapIdentityIncludesAtomId()
    {
        var evaluation = EvaluateAtomIdentityCounterexample();

        AssertGapEffect(
            evaluation,
            "delta-atom:coverage-receipt-mismatch:D5/S0/Carrier/BackfillTarget",
            AdmissionEffect.Observe);
        AssertGapEffect(
            evaluation,
            "second-atom:coverage-receipt-mismatch:D5/S0/Carrier/BackfillTarget",
            AdmissionEffect.Block);
    }

    [Fact]
    public void BaselineComparableReceiptIntegrityCodeSetIsExactlyCoverageReceiptMismatch()
    {
        Assert.Equal(
            new[] { "coverage-receipt-mismatch" },
            BackfillInventoryRule.BaselineComparableReceiptIntegrityCodes.ToArray());
    }

    [Fact]
    public void ReceiptIntegrityGapIdentityIncludesCode()
    {
        var evaluation = EvaluateCodeIdentityCounterexample();

        AssertGapEffect(
            evaluation,
            "delta-atom:coverage-receipt-mismatch:D5/S0/Carrier/BackfillTarget",
            AdmissionEffect.Observe);
        AssertGapEffect(
            evaluation,
            "delta-atom:scribe-emission-mismatch:D5/S0/Carrier/BackfillTarget",
            AdmissionEffect.Block);
    }

    [Fact]
    public void ReceiptIntegrityGapIdentityIncludesCoverageGidDetail()
    {
        var evaluation = EvaluateDetailIdentityCounterexample();

        AssertGapEffect(
            evaluation,
            "delta-atom:coverage-receipt-mismatch:D5/S0/Carrier/BackfillTarget",
            AdmissionEffect.Observe);
        AssertGapEffect(
            evaluation,
            "delta-atom:coverage-receipt-mismatch:D5/S0/Carrier/BackfillTargetB",
            AdmissionEffect.Block);
    }

    [Fact]
    public void NewReceiptIntegrityGapIsBlockingAtSl016Admission()
    {
        var (_, evaluation) = EvaluateReceiptIntegrityGap(
            "coverage-receipt-mismatch",
            gapExistsInBaseline: false);

        var diagnostic = Assert.Single(evaluation.Diagnostics, item => item.Message.Contains(
            "coverage-receipt-mismatch",
            StringComparison.Ordinal));
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
    }

    [Theory]
    [InlineData("scribe-definition-mismatch", false)]
    [InlineData("scribe-emission-mismatch", false)]
    [InlineData("scribe-definition-mismatch", true)]
    [InlineData("scribe-emission-mismatch", true)]
    public void ScribeReceiptIntegrityGapIsAlwaysBlockingAtSl016Admission(
        string mismatchCode,
        bool gapExistsInBaseline)
    {
        var (_, evaluation) = EvaluateReceiptIntegrityGap(
            mismatchCode,
            gapExistsInBaseline);

        var diagnostic = Assert.Single(evaluation.Diagnostics, item => item.Message.Contains(
            mismatchCode,
            StringComparison.Ordinal));
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
    }

    [Fact]
    public void CandidateScribeVerificationKeepsNewGapBlockingAtSl016Admission()
    {
        var (_, evaluation) = EvaluateReceiptIntegrityGap(
            mismatchCode: null,
            gapExistsInBaseline: false,
            candidateScribeInputsChanged: true);

        foreach (var mismatchCode in new[]
                 {
                     "scribe-definition-mismatch",
                     "scribe-emission-mismatch",
                 })
        {
            var diagnostic = Assert.Single(evaluation.Diagnostics, item => item.Message.Contains(
                mismatchCode,
                StringComparison.Ordinal));
            Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        }
    }

    private static (RuleEvaluationContext Context, SingleRuleEvaluation Evaluation)
        EvaluateReceiptIntegrityGap(
            string? mismatchCode,
            bool gapExistsInBaseline,
            bool candidateScribeInputsChanged = false)
    {
        const string atomPath =
            "Meta/Digestion/backfill/delta-v0.1/partial-closed/delta-atom.yaml";
        const string coverageGid = "D5/S0/Carrier/BackfillTarget";
        const string targetPath = coverageGid + ".lean";
        const string baselineDefinition = "fixture Scribe definition\n";
        const string baselineEmission = "# Fixture Scribe emission\n";
        var candidateDefinition = candidateScribeInputsChanged
            ? "changed fixture Scribe definition\n"
            : baselineDefinition;
        var candidateEmission = candidateScribeInputsChanged
            ? "# Changed fixture Scribe emission\n"
            : baselineEmission;
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.UseValidDirectoryBackfill();

        var definitionPath = ScribeEmissionAttestation.DefinitionPath(coverageGid);
        var emissionPath = ScribeEmissionAttestation.EmissionPath(coverageGid);
        var baselineDefinitionSha256 = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(baselineDefinition)).RawSha256;
        var baselineEmissionSha256 = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(baselineEmission)).RawSha256;
        var candidateDefinitionSha256 = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(candidateDefinition)).RawSha256;
        var candidateEmissionSha256 = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(candidateEmission)).RawSha256;
        var targetSha256 = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(fixture.Files[targetPath])).RawSha256;
        var mismatchSha256 = "sha256:" + new string('0', 64);
        foreach (var files in new[] { fixture.Baseline, fixture.ForkPoint })
        {
            files[targetPath] = fixture.Files[targetPath];
            files[definitionPath] = baselineDefinition;
            files[emissionPath] = baselineEmission;
        }
        fixture.Files[definitionPath] = candidateDefinition;
        fixture.Files[emissionPath] = candidateEmission;

        var receiptProjection = "coverage:\n"
            + $"    - gid: {coverageGid}\n"
            + $"      source_sha256: {RuleFixture.FixtureCasReference}\n"
            + $"      target_sha256: {(mismatchCode == "coverage-receipt-mismatch" ? mismatchSha256 : targetSha256)}\n"
            + "  scribe:\n"
            + $"    - gid: {coverageGid}\n"
            + $"      definition_sha256: {(mismatchCode == "scribe-definition-mismatch" ? mismatchSha256 : baselineDefinitionSha256)}\n"
            + $"      emission_sha256: {(mismatchCode == "scribe-emission-mismatch" ? mismatchSha256 : baselineEmissionSha256)}";
        fixture.Files[atomPath] = AddReceipts(fixture.Files[atomPath], receiptProjection);
        if (gapExistsInBaseline || candidateScribeInputsChanged)
        {
            fixture.Baseline[atomPath] = AddReceipts(fixture.Baseline[atomPath], receiptProjection);
            fixture.ForkPoint[atomPath] = AddReceipts(fixture.ForkPoint[atomPath], receiptProjection);
        }

        var verifiedScribeEmissions = VerifiedScribeEmissions.Create(
        [
            new ScribeEmissionRecord(
                coverageGid,
                definitionPath,
                candidateDefinitionSha256,
                emissionPath,
                candidateEmissionSha256),
        ]);
        var changedPaths = gapExistsInBaseline
            ? new[] { "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs" }
            : candidateScribeInputsChanged
                ? new[]
                {
                    "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs",
                    definitionPath,
                    emissionPath,
                }
            : new[]
            {
                "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs",
                atomPath,
            };
        var context = fixture.Build(
            RawChangeSet.Create(changedPaths),
            verifiedScribeEmissions: verifiedScribeEmissions);
        return (
            context,
            RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), context));
    }

    private static string AddReceipts(string atom, string receiptProjection) => atom.Replace(
        "coverage: []\n  scribe: []",
        receiptProjection,
        StringComparison.Ordinal);

    private static (
        RuleFixture Fixture,
        VerifiedScribeEmissions VerifiedScribeEmissions,
        string ReceiptProjection) PreparedDeclarationPairFixture(string gid)
    {
        var fixture = PreparedCoverageFixture();
        var separator = gid.LastIndexOf('.');
        var targetPath = gid[..separator] + ".lean";
        var declaration = gid[(separator + 1)..];
        fixture.Reports[targetPath] = new LeanFileReport(
            [],
            [new LeanDeclaration(declaration, "def", "Unit", [])]);
        var definition = "candidate pair Scribe definition\n";
        var emission = "# Candidate pair Scribe emission\n";
        var documentGid = ScribeEmissionAttestation.DocumentGid(gid);
        var definitionPath = ScribeEmissionAttestation.DefinitionPath(documentGid);
        var emissionPath = ScribeEmissionAttestation.EmissionPath(documentGid);
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[definitionPath] = definition;
            files[emissionPath] = emission;
        }

        var definitionSha256 = Sha256(definition);
        var emissionSha256 = Sha256(emission);
        var targetSha256 = Sha256(fixture.Files[targetPath]);
        var receipts = "coverage:\n"
            + $"    - gid: {gid}\n"
            + $"      source_sha256: {RuleFixture.FixtureCasReference}\n"
            + $"      target_sha256: {targetSha256}\n"
            + "  scribe:\n"
            + $"    - gid: {gid}\n"
            + $"      definition_sha256: {definitionSha256}\n"
            + $"      emission_sha256: {emissionSha256}";
        var verified = VerifiedScribeEmissions.Create(
        [
            new ScribeEmissionRecord(
                documentGid,
                definitionPath,
                definitionSha256,
                emissionPath,
                emissionSha256),
        ],
        [gid]);
        return (fixture, verified, receipts);
    }

    private static string AddCoverageAndReceipts(
        string atom,
        string gid,
        string receiptProjection) => AddReceipts(
            atom.Replace(
                "  - D5/S0/Carrier/BackfillTarget",
                $"  - D5/S0/Carrier/BackfillTarget\n  - {gid}",
                StringComparison.Ordinal),
            receiptProjection);

    private static void AddFormalizationPrecommitment(
        RuleFixture fixture,
        string atomId,
        string gid)
    {
        var separator = gid.LastIndexOf('.');
        var signature = new DigestionFormalizationSignature(
            gid[(separator + 1)..],
            "def",
            "Unit");
        var receipt = new DigestionFormalizationReceipt(
            atomId,
            gid,
            signature,
            RuleFixture.FixtureCasReference,
            RuleFixture.FixtureCasReference);
        var receiptText = Encoding.UTF8.GetString(
            DigestionFormalizationReceipt.Write(receipt).AsSpan());
        var receiptPath = DigestionFormalizationReceipt.PathForAtom(atomId);
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[receiptPath] = receiptText;
        }
    }

    private static SingleRuleEvaluation EvaluateAtomIdentityCounterexample()
    {
        const string atomRoot = "Meta/Digestion/backfill/delta-v0.1/partial-closed/";
        const string firstAtomPath = atomRoot + "delta-atom.yaml";
        const string secondAtomPath = atomRoot + "second-atom.yaml";
        const string coverageGid = "D5/S0/Carrier/BackfillTarget";
        var fixture = PreparedCoverageFixture();
        var targetSha256 = Sha256(fixture.Files[coverageGid + ".lean"]);
        var mismatchSha256 = MismatchSha256();
        var correctReceipt = CoverageReceipt(coverageGid, targetSha256);
        var mismatchedReceipt = CoverageReceipt(coverageGid, mismatchSha256);
        var secondAtom = fixture.Files[firstAtomPath].Replace(
            "ast_path: manual/fixture",
            "ast_path: manual/second-fixture",
            StringComparison.Ordinal);

        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[firstAtomPath] = AddReceipts(files[firstAtomPath], mismatchedReceipt);
            files[secondAtomPath] = AddReceipts(secondAtom, correctReceipt);
        }
        fixture.Files[secondAtomPath] = AddReceipts(secondAtom, mismatchedReceipt);

        return EvaluateSl016(
            fixture,
            VerifiedScribeEmissions.Empty,
            ["tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs", secondAtomPath]);
    }

    private static SingleRuleEvaluation EvaluateCodeIdentityCounterexample()
    {
        const string atomPath =
            "Meta/Digestion/backfill/delta-v0.1/partial-closed/delta-atom.yaml";
        const string coverageGid = "D5/S0/Carrier/BackfillTarget";
        var fixture = PreparedCoverageFixture();
        var definitionPath = ScribeEmissionAttestation.DefinitionPath(coverageGid);
        var emissionPath = ScribeEmissionAttestation.EmissionPath(coverageGid);
        const string definition = "fixture Scribe definition\n";
        const string emission = "# Fixture Scribe emission\n";
        var definitionSha256 = Sha256(definition);
        var emissionSha256 = Sha256(emission);
        var receiptProjection = CoverageReceipt(coverageGid, MismatchSha256())
            .Replace(
                "  scribe: []",
                "  scribe:\n"
                + $"    - gid: {coverageGid}\n"
                + $"      definition_sha256: {definitionSha256}\n"
                + $"      emission_sha256: {emissionSha256}",
                StringComparison.Ordinal);
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[atomPath] = AddReceipts(files[atomPath], receiptProjection);
            files[definitionPath] = definition;
            files[emissionPath] = emission;
        }

        var verified = VerifiedScribeEmissions.Create(
        [
            new ScribeEmissionRecord(
                coverageGid,
                definitionPath,
                definitionSha256,
                emissionPath,
                MismatchSha256()),
        ]);

        return EvaluateSl016(
            fixture,
            verified,
            ["tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs", emissionPath]);
    }

    private static SingleRuleEvaluation EvaluateDetailIdentityCounterexample()
    {
        const string atomPath =
            "Meta/Digestion/backfill/delta-v0.1/partial-closed/delta-atom.yaml";
        const string firstGid = "D5/S0/Carrier/BackfillTarget";
        const string secondGid = "D5/S0/Carrier/BackfillTargetB";
        var fixture = PreparedCoverageFixture();
        AddSecondTarget(fixture, firstGid, secondGid);
        var secondTargetSha256 = Sha256(fixture.Files[secondGid + ".lean"]);
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[atomPath] = files[atomPath].Replace(
                $"  - {firstGid}",
                $"  - {firstGid}\n  - {secondGid}",
                StringComparison.Ordinal);
        }

        var baselineReceipts = CoverageReceipts(
            (firstGid, MismatchSha256()),
            (secondGid, secondTargetSha256));
        var candidateReceipts = CoverageReceipts(
            (firstGid, MismatchSha256()),
            (secondGid, MismatchSha256()));
        fixture.Files[atomPath] = AddReceipts(fixture.Files[atomPath], candidateReceipts);
        fixture.Baseline[atomPath] = AddReceipts(fixture.Baseline[atomPath], baselineReceipts);
        fixture.ForkPoint[atomPath] = AddReceipts(fixture.ForkPoint[atomPath], baselineReceipts);

        return EvaluateSl016(
            fixture,
            VerifiedScribeEmissions.Empty,
            ["tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs", atomPath]);
    }

    private static RuleFixture PreparedCoverageFixture()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.UseValidDirectoryBackfill();
        const string targetPath = "D5/S0/Carrier/BackfillTarget.lean";
        foreach (var files in new[] { fixture.Baseline, fixture.ForkPoint })
        {
            files[targetPath] = fixture.Files[targetPath];
        }
        return fixture;
    }

    private static void AddSecondTarget(RuleFixture fixture, string firstGid, string secondGid)
    {
        var firstPath = firstGid + ".lean";
        var secondPath = secondGid + ".lean";
        fixture.Files[secondPath] = fixture.Files[firstPath].Replace(
            firstGid,
            secondGid,
            StringComparison.Ordinal);
        fixture.Reports[secondPath] = fixture.Reports[firstPath];
        foreach (var files in new[] { fixture.Baseline, fixture.ForkPoint })
        {
            files[secondPath] = fixture.Files[secondPath];
        }
    }

    private static SingleRuleEvaluation EvaluateSl016(
        RuleFixture fixture,
        VerifiedScribeEmissions verified,
        string[] changedPaths)
    {
        var context = fixture.Build(
            RawChangeSet.Create(changedPaths),
            verifiedScribeEmissions: verified);
        return RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(16), context);
    }

    private static void AssertGapEffect(
        SingleRuleEvaluation evaluation,
        string message,
        AdmissionEffect effect)
    {
        var diagnostic = Assert.Single(evaluation.Diagnostics, item =>
            string.Equals(item.Message, message, StringComparison.Ordinal));
        Assert.Equal(effect, diagnostic.AdmissionEffect);
    }

    private static string CoverageReceipt(string gid, string targetSha256) =>
        CoverageReceipts((gid, targetSha256));

    private static string CoverageReceipts(params (string Gid, string TargetSha256)[] receipts) =>
        "coverage:\n"
        + string.Concat(receipts.Select(static receipt =>
            $"    - gid: {receipt.Gid}\n"
            + $"      source_sha256: {RuleFixture.FixtureCasReference}\n"
            + $"      target_sha256: {receipt.TargetSha256}\n"))
        + "  scribe: []";

    private static string Sha256(string text) =>
        DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(text)).RawSha256;

    private static string MismatchSha256() => "sha256:" + new string('0', 64);

}
