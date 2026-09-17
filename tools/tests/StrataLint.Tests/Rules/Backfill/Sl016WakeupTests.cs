using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

// SL-016 的唤醒路径。独立成文件而非并入 RuleEngineTests:后者已达 SL-003 硬线 800 行,
// 按 CLAUDE.md 第 8 条「桶满则裂、只裂不迁」,新条目入新桶,既有条目原地不动。
public sealed class Sl016WakeupTests
{
    private const string AtomPath =
        "Meta/Digestion/backfill/delta-v0.1/partial-open/"
        + RuleFixture.FixtureAtomId
        + ".yaml";
    // A family pattern must wake the rule for a new volume without a literal FILEMAP entry.
    [Fact]
    public void TheoryVolumeChangeWakesSl016ThroughFileMapSourcePattern()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.Create(
            ["docs/develop/theory/INTERFACE_PAPER.md"]));

        Assert.True(context.Policy.IsDigestionSource(RepoPath.CreateKnown("docs/develop/theory/INTERFACE_PAPER.md")));
        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
    }

    // CAS bytes can change the atom projection independently of source-document changes.
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
        var document = BackfillInventoryLoader.LoadCandidateDelta(
            context.Current,
            context.Baseline,
            context.Changes);
        var impact = BackfillDeltaImpactResolver.Resolve(
            context.Current,
            context.Baseline,
            context.Lean.Report,
            document,
            context.Changes);

        Assert.False(impact.HasAffectedEdges);
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
                "coverage-target-mismatch",
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
                "coverage-target-mismatch",
                StringComparison.Ordinal));
    }

    [Fact]
    public void ReferencedCasContentChangeStillWakesAndJudgesEdge()
    {
        var fixture = CoverageReceiptFixture(
            "D5/S0/Carrier/BackfillTarget",
            FrozenStatementReceiptTestData.Id('0'));
        fixture.Baseline.Remove(RuleFixture.FixtureCasPath);
        var context = fixture.Build(RawChangeSet.CreateWithKinds(
            [(RuleFixture.FixtureCasPath, RawChangeKind.Added)]));
        var document = BackfillInventoryLoader.LoadCandidateDelta(
            context.Current,
            context.Baseline,
            context.Changes);
        var impact = BackfillDeltaImpactResolver.Resolve(
            context.Current,
            context.Baseline,
            context.Lean.Report,
            document,
            context.Changes);
        var entry = Assert.Single(document.RequireDigestionEntries());

        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
        Assert.True(DigestionCasStore.EntryChanged(entry, impact.EvaluationChanges));
        Assert.Contains(
            BackfillInventoryRule.EvaluateCandidateDelta(context),
            static finding => finding.Message.Contains(
                "coverage-target-mismatch",
                StringComparison.Ordinal));
    }

     [Fact]
    public void LeanHeaderChangeWithStableTargetValueDoesNotWakeReferencedEdge()
    {
        const string targetGid = "D5/S0/Carrier/BackfillTarget";
        var targetPath = targetGid + ".lean";
        var fixture = CoverageReceiptFixture(
            targetGid,
            FrozenStatementReceiptTestData.Id('a'));
        fixture.Files[targetPath] += "\n-- candidate value change\n";
        var context = fixture.Build(RawChangeSet.Create([targetPath]));
        var document = BackfillInventoryLoader.LoadCandidateDelta(
            context.Current,
            context.Baseline,
            context.Changes);
        var impact = BackfillDeltaImpactResolver.Resolve(
            context.Current,
            context.Baseline,
            context.Lean.Report,
            document,
            context.Changes);
        var entry = Assert.Single(document.RequireDigestionEntries());

        Assert.False(impact.HasAffectedEdges);
        Assert.False(DigestionCasStore.EntryChanged(entry, impact.EvaluationChanges));
    }

    [Fact]
    public void ReportFreeIngestDoesNotComparePersistedTargetAgainstMissingReport()
    {
        const string targetGid = "D5/S0/Carrier/BackfillTarget";
        var fixture = CoverageReceiptFixture(
            targetGid,
            FrozenStatementReceiptTestData.Id('a'));
        var context = fixture.Build(RawChangeSet.Create(["README.md"]));
        var document = BackfillInventoryLoader.LoadCandidateDelta(
            context.Current,
            context.Baseline,
            context.Changes);

        var impact = BackfillDeltaImpactResolver.Resolve(
            context.Current,
            context.Baseline,
            report: null,
            document,
            context.Changes);

        Assert.False(impact.HasAffectedEdges);
        Assert.False(DigestionCasStore.EntryChanged(
            Assert.Single(document.RequireDigestionEntries()),
            impact.EvaluationChanges));
    }

    [Fact]
    public void ReportFreeFrozenModuleStatementIdChangeWakesReferencedEdge()
    {
        const string targetGid = "D5/S0/Carrier/BackfillTarget";
        var fixture = CoverageReceiptFixture(
            targetGid,
            FrozenStatementReceiptTestData.Id('a'));
        InstallFrozenModulesInto(
            fixture.Files,
            FrozenModule(targetGid, FrozenStatementReceiptTestData.Id('b')));
        var context = fixture.Build(RawChangeSet.Create(FrozenLedgerDelta(fixture)));
        var document = BackfillInventoryLoader.LoadCandidateDelta(
            context.Current,
            context.Baseline,
            context.Changes);

        var impact = BackfillDeltaImpactResolver.Resolve(
            context.Current,
            context.Baseline,
            report: null,
            document,
            context.Changes);

        Assert.True(impact.HasAffectedEdges);
        Assert.Contains(impact.EvaluationChanges.Paths, path => path.Value == AtomPath);
    }

    [Fact]
    public void UnrelatedD5ModuleDoesNotDeriveCoverageTargetValue()
    {
        const string targetGid = "D5/S0/Carrier/BackfillTarget";
        var fixture = CoverageReceiptFixture(
            targetGid,
            FrozenStatementReceiptTestData.Id('a'));
        var context = fixture.Build(RawChangeSet.Create(["D5/S3/Probe/Unrelated.lean"]));
        var document = BackfillInventoryLoader.LoadCandidateDelta(
            context.Current,
            context.Baseline,
            context.Changes);
        var derivations = 0;

        var impact = BackfillDeltaImpactResolver.Resolve(
            context.Current,
            context.Baseline,
            context.Lean.Report,
            document,
            context.Changes,
            _ => derivations++);

        Assert.Equal(0, derivations);
        Assert.False(impact.HasAffectedEdges);
    }

    [Fact]
    public void ChangedHostModuleDerivesOnlyReverseIndexedCoverageTarget()
    {
        const string targetGid = "D5/S0/Carrier/BackfillTarget";
        const string otherGid = "D5/S0/Carrier/UnrelatedTarget";
        var fixture = CoverageReceiptFixture(
            targetGid,
            FrozenStatementReceiptTestData.Id('a'));
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[AtomPath] = files[AtomPath].Replace(
                "receipts:\n",
                $"  - gid: {otherGid}\n"
                    + $"    target_statement_id: {FrozenStatementReceiptTestData.Id('c')}\n"
                    + "receipts:\n",
                StringComparison.Ordinal);
            InstallFrozenModulesInto(
                files,
                FrozenModule(targetGid, FrozenStatementReceiptTestData.Id('a')),
                FrozenModule(otherGid, FrozenStatementReceiptTestData.Id('c')));
        }
        var context = fixture.Build(RawChangeSet.Create([targetGid + ".lean"]));
        var document = BackfillInventoryLoader.LoadCandidateDelta(
            context.Current,
            context.Baseline,
            context.Changes);
        var derivedGids = new List<string>();

        _ = BackfillDeltaImpactResolver.Resolve(
            context.Current,
            context.Baseline,
            context.Lean.Report,
            document,
            context.Changes,
            derivedGids.Add);

        Assert.Equal([targetGid], derivedGids);
    }

    [Fact]
    public void EntryLocalChangeDoesNotDeriveSharedCoverageGidOrWakePeer()
    {
        const string targetGid = "D5/S0/Carrier/BackfillTarget";
        var fixture = CoverageReceiptFixture(
            targetGid,
            FrozenStatementReceiptTestData.Id('a'));
        var otherFingerprint = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes("shared coverage peer\n"));
        var otherAtomPath = BackfillInventoryLoader.RootPath
            + "delta-v0.1/partial-open/"
            + otherFingerprint.RawSha256["sha256:".Length..]
            + ".yaml";
        var otherCasPath = DigestionCasStore.RootPath
            + otherFingerprint.RawSha256["sha256:".Length..];
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[otherAtomPath] = files[AtomPath]
                .Replace(
                    RuleFixture.FixtureCasReference,
                    otherFingerprint.RawSha256,
                    StringComparison.Ordinal)
                .Replace(
                    "target_statement_id: " + FrozenStatementReceiptTestData.Id('a'),
                    "target_statement_id: " + FrozenStatementReceiptTestData.Id('c'),
                    StringComparison.Ordinal);
            files[otherCasPath] = "shared coverage peer\n";
        }
        fixture.Files[AtomPath] = fixture.Files[AtomPath].Replace(
            "unresolved_subitems: []",
            "unresolved_subitems:\n    - entry-local-change",
            StringComparison.Ordinal);
        var context = fixture.Build(RawChangeSet.Create([AtomPath]));
        var document = BackfillInventoryLoader.LoadCandidateDelta(
            context.Current,
            context.Baseline,
            context.Changes);
        var derivations = 0;

        var impact = BackfillDeltaImpactResolver.Resolve(
            context.Current,
            context.Baseline,
            context.Lean.Report,
            document,
            context.Changes,
            _ => derivations++);

        Assert.Equal(0, derivations);
        Assert.Contains(impact.EvaluationChanges.Paths, path => path.Value == AtomPath);
        Assert.DoesNotContain(impact.EvaluationChanges.Paths, path => path.Value == otherAtomPath);
    }

    [Fact]
    public void UnchangedBaseEntryDuplicateCoverageFailsClosedAtLoad()
    {
        var fixture = new RuleFixture();
        fixture.UseValidDirectoryBackfill();
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[AtomPath] = files[AtomPath].Replace(
                "coverage_gids:\n  - gid: D5/S0/Carrier/BackfillTarget\n    target_statement_id: null",
                "coverage_gids:\n  - gid: D5/S0/Carrier/BackfillTarget\n    target_statement_id: null\n"
                    + "  - gid: D5/S0/Carrier/BackfillTarget\n    target_statement_id: null",
                StringComparison.Ordinal);
        }

        var findings = BackfillInventoryRule.EvaluateCandidateDelta(
            fixture.Build(RawChangeSet.Create(["D5/S3/Probe/Unrelated.lean"])));

        Assert.Contains(findings, finding => finding.Message.Contains(
            "BACKFILL_COVERAGE_ORDER",
            StringComparison.Ordinal));
    }

    [Fact]
    public void ChangedEntryDuplicateCoverageStillProducesFinding()
    {
        var fixture = new RuleFixture();
        fixture.UseValidDirectoryBackfill();
        fixture.Files[AtomPath] = fixture.Files[AtomPath].Replace(
            "coverage_gids:\n  - gid: D5/S0/Carrier/BackfillTarget\n    target_statement_id: null",
            "coverage_gids:\n  - gid: D5/S0/Carrier/BackfillTarget\n    target_statement_id: null\n"
                + "  - gid: D5/S0/Carrier/BackfillTarget\n    target_statement_id: null",
            StringComparison.Ordinal);

        var findings = BackfillInventoryRule.EvaluateCandidateDelta(
            fixture.Build(RawChangeSet.Create([AtomPath])));

        Assert.Contains(findings, finding => finding.Message.Contains(
            "BACKFILL_COVERAGE_ORDER",
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
    public void RuleImplementationChangeStillValidatesCurrentCoverageEdges()
    {
        var (context, evaluation) = EvaluateReceiptIntegrityGap(
            "coverage-target-mismatch",
            gapExistsInBaseline: true);

        Assert.True(context.RuleImplementationChanged);
        Assert.Contains(evaluation.Diagnostics, item => item.Message.Contains(
            "coverage-target-mismatch",
            StringComparison.Ordinal));
    }

    [Fact]
    public void FullEvaluateRemainsAvailableForProducerRecomputation()
    {
        var (context, _) = EvaluateReceiptIntegrityGap(
            "coverage-target-mismatch",
            gapExistsInBaseline: true);

        Assert.Contains(
            BackfillInventoryRule.Evaluate(context),
            static finding => finding.Message.Contains(
                "coverage-target-mismatch",
                StringComparison.Ordinal));
    }

    [Fact]
    public void NewReceiptIntegrityGapIsBlockingAtSl016Admission()
    {
        var (_, evaluation) = EvaluateReceiptIntegrityGap(
            "coverage-target-mismatch",
            gapExistsInBaseline: false);

        var diagnostic = Assert.Single(evaluation.Diagnostics, item => item.Message.Contains(
            "coverage-target-mismatch",
            StringComparison.Ordinal));
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
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
        foreach (var files in new[] { fixture.Baseline })
        {
            files[targetPath] = fixture.Files[targetPath];
            files[definitionPath] = baselineDefinition;
            files[emissionPath] = baselineEmission;
        }
        fixture.Files[definitionPath] = candidateDefinition;
        fixture.Files[emissionPath] = candidateEmission;

        var receiptProjection = "coverage_gids:\n"
            + $"  - gid: {coverageGid}\n"
            + $"    target_statement_id: {(mismatchCode == "coverage-target-mismatch" ? mismatchSha256 : targetStatementId)}\n"
            + "receipts:\n";
        fixture.Files[AtomPath] = AddReceipts(fixture.Files[AtomPath], receiptProjection);
        if (gapExistsInBaseline || candidateScribeInputsChanged)
        {
            fixture.Baseline[AtomPath] = AddReceipts(fixture.Baseline[AtomPath], receiptProjection);
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
        "coverage_gids:\n"
            + "  - gid: D5/S0/Carrier/BackfillTarget\n"
            + "    target_statement_id: null\n"
            + "receipts:\n",
        receiptProjection,
        StringComparison.Ordinal);

    private static RuleFixture PreparedCoverageFixture()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.UseValidDirectoryBackfill();
        InstallFrozenModules(fixture, "D5/S0/Carrier/BackfillTarget");
        const string targetPath = "D5/S0/Carrier/BackfillTarget.lean";
        foreach (var files in new[] { fixture.Baseline })
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
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            InstallFrozenModulesInto(files, modules);
        }
    }

    private static RuleFixture CoverageReceiptFixture(string targetGid, string targetStatementId)
    {
        var fixture = PreparedCoverageFixture();
        var receipt = "coverage_gids:\n"
            + $"  - gid: {targetGid}\n"
            + $"    target_statement_id: {targetStatementId}\n"
            + "receipts:\n";
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[AtomPath] = AddReceipts(files[AtomPath], receipt);
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
            .Where(static path => FrozenLedgerChangeClassifier.IsAcceptedEventPath(path)
                || FrozenStatePath.IsUnderRoot(path));
        var baseline = fixture.Baseline.Keys
            .Where(static path => FrozenLedgerChangeClassifier.IsAcceptedEventPath(path)
                || FrozenStatePath.IsUnderRoot(path));
        var delta = current
            .Except(baseline, StringComparer.Ordinal)
            .Concat(baseline.Except(current, StringComparer.Ordinal))
            .Concat(current.Intersect(baseline, StringComparer.Ordinal).Where(path =>
                !string.Equals(
                    fixture.Files[path],
                    fixture.Baseline[path],
                    StringComparison.Ordinal)))
            .ToArray();
        Assert.NotEmpty(delta);
        return delta;
    }

}
