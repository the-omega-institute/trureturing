using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

// SL-016 的唤醒路径。独立成文件而非并入 RuleEngineTests:后者已达 SL-003 硬线 800 行,
// 按 CLAUDE.md 第 8 条「桶满则裂、只裂不迁」,新条目入新桶,既有条目原地不动。
public sealed class Sl016WakeupTests
{
    private const string AtomPath =
        "Meta/Digestion/backfill/delta-v0.1/partial-closed/"
        + RuleFixture.FixtureAtomId
        + ".yaml";
    private const string SecondAtomId =
        "16367aacb67a4a017c8da8ab95682ccb390863780f7114dda0a0e0c55644c7c4";
    private const string SecondCasReference = "sha256:" + SecondAtomId;
    private const string SecondCasPath = "Meta/Digestion/atoms/sha256/" + SecondAtomId;

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
    public void FrozenShardPathChangeWithStableStatementIdDoesNotWakeReferencedEdge()
    {
        const string targetGid = "D5/S0/Carrier/BackfillTarget";
        var fixture = CoverageReceiptFixture(targetGid, FrozenStatementReceiptTestData.Id('a'));
        InstallFrozenModulesInto(
            fixture.Files,
            FrozenModule(targetGid, FrozenStatementReceiptTestData.Id('a')),
            FrozenModule("D5/S0/Carrier/Unrelated", FrozenStatementReceiptTestData.Id('c')));
        var context = fixture.Build(RawChangeSet.Create(FrozenLedgerDelta(fixture)));

        Assert.False(BackfillInventoryRule.IsAffectedBy(context));
    }

    [Fact]
    public void FrozenStatementIdChangeStillWakesAndJudgesReferencedEdge()
    {
        const string targetGid = "D5/S0/Carrier/BackfillTarget";
        var baselineStatementId = FrozenStatementReceiptTestData.Id('a');
        var fixture = CoverageReceiptFixture(targetGid, baselineStatementId);
        InstallFrozenModulesInto(
            fixture.Files,
            FrozenModule(targetGid, FrozenStatementReceiptTestData.Id('b')));
        var context = fixture.Build(RawChangeSet.Create(FrozenLedgerDelta(fixture)));

        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
        Assert.Contains(
            BackfillInventoryRule.EvaluateCandidateDelta(context),
            static finding => finding.Message.Contains(
                "coverage-receipt-mismatch",
                StringComparison.Ordinal));
    }

    [Fact]
    public void EdgeFileInDeltaStillWakesAndJudgesSl016()
    {
        var fixture = CoverageReceiptFixture(
            "D5/S0/Carrier/BackfillTarget",
            FrozenStatementReceiptTestData.Id('0'));
        var context = fixture.Build(RawChangeSet.Create([AtomPath]));

        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
        Assert.Contains(
            BackfillInventoryRule.EvaluateCandidateDelta(context),
            static finding => finding.Message.Contains(
                "coverage-receipt-mismatch",
                StringComparison.Ordinal));
    }

    [Fact]
    public void ReferencedCasContentChangeStillWakesAndJudgesEdge()
    {
        var fixture = CoverageReceiptFixture(
            "D5/S0/Carrier/BackfillTarget",
            FrozenStatementReceiptTestData.Id('0'));
        fixture.Baseline.Remove(RuleFixture.FixtureCasPath);
        fixture.ForkPoint.Remove(RuleFixture.FixtureCasPath);
        var context = fixture.Build(RawChangeSet.CreateWithKinds(
            [(RuleFixture.FixtureCasPath, RawChangeKind.Added)]));
        var document = BackfillInventoryLoader.LoadCandidateDelta(
            context.Current,
            context.Baseline,
            context.Changes);
        var impact = BackfillDeltaImpactResolver.Resolve(
            context.Current,
            context.Baseline,
            document,
            context.Changes);
        var entry = Assert.Single(document.RequireDigestionEntries());

        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
        Assert.True(DigestionCasStore.EntryChanged(entry, impact.EvaluationChanges));
        Assert.Contains(
            BackfillInventoryRule.EvaluateCandidateDelta(context),
            static finding => finding.Message.Contains(
                "coverage-receipt-mismatch",
                StringComparison.Ordinal));
    }

    [Fact]
    public void ReferencedScribeEmissionChangeStillWakesAndJudgesEdge()
    {
        var (context, evaluation) = EvaluateReceiptIntegrityGap(
            mismatchCode: null,
            gapExistsInBaseline: true,
            candidateScribeInputsChanged: true,
            candidateScribeEmissionOnly: true);
        var document = BackfillInventoryLoader.LoadCandidateDelta(
            context.Current,
            context.Baseline,
            context.Changes);
        var impact = BackfillDeltaImpactResolver.Resolve(
            context.Current,
            context.Baseline,
            document,
            context.Changes);

        Assert.True(DigestionCasStore.EntryChanged(
            Assert.Single(document.RequireDigestionEntries()),
            impact.EvaluationChanges));
        Assert.Contains(evaluation.Diagnostics, static finding => finding.Message.Contains(
            "scribe-emission-mismatch",
            StringComparison.Ordinal));
    }

    [Fact]
    public void UnchangedBaseEntryDuplicateCoverageIsNotRepublishedForUnrelatedDelta()
    {
        var fixture = new RuleFixture();
        fixture.UseValidDirectoryBackfill();
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[AtomPath] = files[AtomPath].Replace(
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
        fixture.Files[AtomPath] = fixture.Files[AtomPath].Replace(
            "coverage_gids:\n  - D5/S0/Carrier/BackfillTarget",
            "coverage_gids:\n  - D5/S0/Carrier/BackfillTarget\n  - D5/S0/Carrier/BackfillTarget",
            StringComparison.Ordinal);

        var findings = BackfillInventoryRule.EvaluateCandidateDelta(
            fixture.Build(RawChangeSet.Create([AtomPath])));

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
        const string gid = "D5/S0/Carrier/BackfillTarget.protectedTargetFixture";
        var (fixture, verifiedScribeEmissions, receiptProjection) =
            PreparedDeclarationPairFixture(gid);
        fixture.Files[AtomPath] = AddCoverageAndReceipts(
            fixture.Files[AtomPath],
            gid,
            receiptProjection);

        var evaluation = EvaluateSl016(
            fixture,
            verifiedScribeEmissions,
            [AtomPath]);

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
        const string secondAtomPath =
            "Meta/Digestion/backfill/delta-v0.1/partial-closed/" + SecondAtomId + ".yaml";
        const string gid = "D5/S0/Carrier/BackfillTarget.protectedTargetFixture";
        var (fixture, verifiedScribeEmissions, receiptProjection) =
            PreparedDeclarationPairFixture(gid);
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[AtomPath] = AddCoverageAndReceipts(
                files[AtomPath],
                gid,
                receiptProjection);
        }

        AddFormalizationPrecommitment(fixture, RuleFixture.FixtureAtomId, gid);
        fixture.Files[secondAtomPath] = fixture.Files[AtomPath].Replace(
            RuleFixture.FixtureCasReference,
            SecondCasReference,
            StringComparison.Ordinal);
        fixture.Files[SecondCasPath] = "second";

        var evaluation = EvaluateSl016(
            fixture,
            verifiedScribeEmissions,
            [secondAtomPath]);

        Assert.Contains(evaluation.Diagnostics, finding =>
            finding.AdmissionEffect == AdmissionEffect.Block
            && finding.Message.Contains(SecondAtomId, StringComparison.Ordinal)
            && finding.Message.Contains(gid, StringComparison.Ordinal)
            && finding.Message.Contains(
                "base-owned formalization precommitment",
                StringComparison.Ordinal));
    }

    [Fact]
    public void ExistingCoveragePairReboundToNewRawFingerprintRequiresNewPrecommitment()
    {
        const string gid = "D5/S0/Carrier/BackfillTarget.protectedTargetFixture";
        var (fixture, _, receiptProjection) = PreparedDeclarationPairFixture(gid);
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[AtomPath] = AddCoverageAndReceipts(files[AtomPath], gid, receiptProjection);
        }
        AddFormalizationPrecommitment(fixture, RuleFixture.FixtureAtomId, gid);
        var reboundFingerprint = "sha256:" + new string('9', 64);
        fixture.Files[AtomPath] = fixture.Files[AtomPath].Replace(
            RuleFixture.FixtureCasReference,
            reboundFingerprint,
            StringComparison.Ordinal);
        var context = fixture.Build(RawChangeSet.Create([AtomPath]));

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
        const string gid = "D5/S0/Carrier/BackfillTarget.protectedTargetFixture";
        var (fixture, _, receiptProjection) = PreparedDeclarationPairFixture(gid);
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[AtomPath] = AddCoverageAndReceipts(files[AtomPath], gid, receiptProjection);
        }

        var reboundFingerprint = "sha256:" + new string('9', 64);
        fixture.Files[AtomPath] = fixture.Files[AtomPath].Replace(
            $"source_sha256: {RuleFixture.FixtureCasReference}",
            $"source_sha256: {reboundFingerprint}",
            StringComparison.Ordinal);
        var context = fixture.Build(RawChangeSet.Create([AtomPath]));

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
        const string gid = "D5/S0/Carrier/BackfillTarget.protectedTargetFixture";
        var (fixture, _, receiptProjection) = PreparedDeclarationPairFixture(gid);
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[AtomPath] = AddCoverageAndReceipts(files[AtomPath], gid, receiptProjection);
        }
        var context = fixture.Build(RawChangeSet.Create([AtomPath]));

        var findings = DigestionFormalizationPrecommitmentValidator.ValidateNewEdges(
            BackfillInventoryLoader.LoadBaseline(context.Baseline),
            BackfillInventoryLoader.Load(context.Current),
            context.Baseline,
            context.Lean.Report);

        Assert.Empty(findings);
    }

    [Fact]
    public void RuleImplementationChangeStillEvaluatesOnlyCandidateDelta()
    {
        var (context, evaluation) = EvaluateReceiptIntegrityGap(
            "coverage-receipt-mismatch",
            gapExistsInBaseline: true);

        Assert.True(context.RuleImplementationChanged);
        Assert.DoesNotContain(evaluation.Diagnostics, item => item.Message.Contains(
            "coverage-receipt-mismatch",
            StringComparison.Ordinal));
    }

    [Fact]
    public void FullEvaluateRemainsAvailableForProducerRecomputation()
    {
        var (context, _) = EvaluateReceiptIntegrityGap(
            "coverage-receipt-mismatch",
            gapExistsInBaseline: true);

        Assert.Contains(
            BackfillInventoryRule.Evaluate(context),
            static finding => finding.Message.Contains(
                "coverage-receipt-mismatch",
                StringComparison.Ordinal));
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
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void ChangedEdgeScribeReceiptIntegrityGapIsBlockingAtSl016Admission(
        string mismatchCode)
    {
        var (_, evaluation) = EvaluateReceiptIntegrityGap(
            mismatchCode,
            gapExistsInBaseline: false);

        var diagnostic = Assert.Single(evaluation.Diagnostics, item => item.Message.Contains(
            mismatchCode,
            StringComparison.Ordinal));
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
    }

    [Theory]
    [InlineData("scribe-definition-mismatch")]
    [InlineData("scribe-emission-mismatch")]
    public void RuleImplementationChangeDoesNotRepublishHistoricalScribeGap(
        string mismatchCode)
    {
        var (context, evaluation) = EvaluateReceiptIntegrityGap(
            mismatchCode,
            gapExistsInBaseline: true);

        Assert.True(context.RuleImplementationChanged);
        Assert.DoesNotContain(evaluation.Diagnostics, item => item.Message.Contains(
            mismatchCode,
            StringComparison.Ordinal));
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
            bool candidateScribeInputsChanged = false,
            bool candidateScribeEmissionOnly = false)
    {
        const string coverageGid = "D5/S0/Carrier/BackfillTarget";
        const string targetPath = coverageGid + ".lean";
        const string baselineDefinition = "fixture Scribe definition\n";
        const string baselineEmission = "# Fixture Scribe emission\n";
        var candidateDefinition = candidateScribeInputsChanged && !candidateScribeEmissionOnly
            ? "changed fixture Scribe definition\n"
            : baselineDefinition;
        var candidateEmission = candidateScribeInputsChanged
            ? "# Changed fixture Scribe emission\n"
            : baselineEmission;
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.UseValidDirectoryBackfill();
        InstallFrozenModules(fixture, coverageGid);

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
        var targetStatementId = FrozenStatementReceiptTestData.Resolve(
            fixture.Files,
            coverageGid);
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
            + $"      target_statement_id: {(mismatchCode == "coverage-receipt-mismatch" ? mismatchSha256 : targetStatementId)}\n"
            + "  scribe:\n"
            + $"    - gid: {coverageGid}\n"
            + $"      definition_sha256: {(mismatchCode == "scribe-definition-mismatch" ? mismatchSha256 : baselineDefinitionSha256)}\n"
            + $"      emission_sha256: {(mismatchCode == "scribe-emission-mismatch" ? mismatchSha256 : baselineEmissionSha256)}";
        fixture.Files[AtomPath] = AddReceipts(fixture.Files[AtomPath], receiptProjection);
        if (gapExistsInBaseline || candidateScribeInputsChanged)
        {
            fixture.Baseline[AtomPath] = AddReceipts(fixture.Baseline[AtomPath], receiptProjection);
            fixture.ForkPoint[AtomPath] = AddReceipts(fixture.ForkPoint[AtomPath], receiptProjection);
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
        var changedPaths = candidateScribeInputsChanged
            ? candidateScribeEmissionOnly
                ? new[]
                {
                    "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs",
                    emissionPath,
                }
                : new[]
                {
                    "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs",
                    definitionPath,
                    emissionPath,
                }
            : gapExistsInBaseline
                ? new[] { "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs" }
            : new[]
            {
                "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs",
                AtomPath,
            };
        var context = fixture.Build(
            RawChangeSet.Create(changedPaths),
            verifiedScribeEmissions: verifiedScribeEmissions);
        var diagnostics = BackfillInventoryRule.EvaluateCandidateDelta(context)
            .Select(static finding => new Diagnostic(
                RuleId.CreateKnown(16),
                "Digestion ledger",
                DisplaySeverity.Error,
                finding.Effect ?? AdmissionEffect.Block,
                finding.Path,
                finding.Message))
            .ToImmutableArray();
        return (
            context,
            new SingleRuleEvaluation(diagnostics, DeferredCase: null));
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
        var targetStatementId = FrozenStatementReceiptTestData.Resolve(fixture.Files, gid);
        var receipts = "coverage:\n"
            + $"    - gid: {gid}\n"
            + $"      source_sha256: {RuleFixture.FixtureCasReference}\n"
            + $"      target_statement_id: {targetStatementId}\n"
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

    private static RuleFixture PreparedCoverageFixture()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.UseValidDirectoryBackfill();
        InstallFrozenModules(fixture, "D5/S0/Carrier/BackfillTarget");
        const string targetPath = "D5/S0/Carrier/BackfillTarget.lean";
        foreach (var files in new[] { fixture.Baseline, fixture.ForkPoint })
        {
            files[targetPath] = fixture.Files[targetPath];
        }
        return fixture;
    }

    private static void InstallFrozenModules(RuleFixture fixture, params string[] moduleGids)
    {
        var modules = moduleGids.Select(gid => FrozenModule(
                gid,
                FrozenStatementReceiptTestData.Id('a')))
            .ToArray();
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            InstallFrozenModulesInto(files, modules);
        }
    }

    private static RuleFixture CoverageReceiptFixture(string targetGid, string targetStatementId)
    {
        var fixture = PreparedCoverageFixture();
        var receipt = "coverage:\n"
            + $"    - gid: {targetGid}\n"
            + $"      source_sha256: {RuleFixture.FixtureCasReference}\n"
            + $"      target_statement_id: {targetStatementId}\n"
            + "  scribe: []";
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            files[AtomPath] = files[AtomPath].Replace(
                "coverage: []\n  scribe: []",
                receipt,
                StringComparison.Ordinal);
        }

        return fixture;
    }

    private static FrozenStatementReceiptTestData.Module FrozenModule(
        string gid,
        string statementId) =>
        new(
            gid + ".lean",
            statementId,
            [
                new FrozenStatementReceiptTestData.Declaration(
                    "protectedTargetFixture",
                    FrozenStatementReceiptTestData.Id('b')),
            ]);

    private static void InstallFrozenModulesInto(
        IDictionary<string, string> files,
        params FrozenStatementReceiptTestData.Module[] modules)
    {
        foreach (var path in files.Keys
                     .Where(static path => FrozenLedgerChangeClassifier.IsAcceptedEventPath(path))
                     .ToArray())
        {
            files.Remove(path);
        }
        FrozenStatementReceiptTestData.AddLedger(files, modules);
    }

    private static string[] FrozenLedgerDelta(RuleFixture fixture)
    {
        var current = fixture.Files.Keys
            .Where(static path => FrozenLedgerChangeClassifier.IsAcceptedEventPath(path));
        var baseline = fixture.Baseline.Keys
            .Where(static path => FrozenLedgerChangeClassifier.IsAcceptedEventPath(path));
        var delta = current
            .Except(baseline, StringComparer.Ordinal)
            .Concat(baseline.Except(current, StringComparer.Ordinal))
            .ToArray();
        Assert.NotEmpty(delta);
        return delta;
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

    private static string Sha256(string text) =>
        DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(text)).RawSha256;

}
