using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;

namespace StrataLint.Tests;

// DigestionLedgerTests 的后半:coverage 派生一族。
// 余量:宿主原 781 行,离 SL-003 的 800 行硬线 19 行。该类本就是 partial。
// 切点判据 = 缩进 4 的真方法收尾 ∧ 后空行 ∧ 再后是缩进 4 的特性行(14 处候选取中点)。

public sealed partial class DigestionLedgerTests
{
    [Fact]
    public void NullTargetForUnfrozenCoverageDerivesPartialOpen()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        var snapshot = Snapshot(
            ("docs/source.md", source),
            CasFile(atom),
            ("D5/X_Frontier/Probe.lean", Encoding.UTF8.GetBytes(Lean("D5/X_Frontier/Probe"))));
        var lean = AcceptedLean("D5/X_Frontier/Probe.lean");
        var ledger = Ledger(
            atom,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed);

        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            ledger,
            snapshot,
            lean);
        var status = Assert.Single(evaluation.Entries);

        Assert.Equal(DigestionMigrationState.Partial, status.DerivedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, status.DerivedStatus.Truth);
        Assert.False(status.Deletable);
        Assert.Contains(status.Gaps, gap => gap.Code == "target-statement-unresolved");
        Assert.DoesNotContain(status.Gaps, gap => gap.Code == "coverage-target-mismatch");
        Assert.Contains(evaluation.Findings, finding =>
            finding.Contains("handwritten status", StringComparison.Ordinal));
    }

    [Fact]
    public void ReproducibleExtractionWithoutSemanticTargetRemainsResidual()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        var ledger = Ledger(
            atom,
            DigestionMigrationState.Residual,
            DigestionTruthState.Open,
            includeCoverageGid: false);

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            ledger,
            Snapshot(("docs/source.md", source), CasFile(atom)),
            AcceptedLean(Array.Empty<string>())).Entries);

        Assert.Equal(DigestionMigrationState.Residual, status.DerivedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, status.DerivedStatus.Truth);
        Assert.Contains(status.Gaps, gap => gap.Code == "coverage-gid-missing");
    }

    [Fact]
    public void UnregisteredGenreDebtDoesNotChangeClosedTruthButPreventsDeletion()
    {
        const string token = "**新判词。**";
        const string gid = "D5/S0/Carrier/Probe";
        const string targetPath = "D5/S0/Carrier/Probe.lean";
        var source = Encoding.UTF8.GetBytes($"# Observer\n\n{token} claim。\n");
        var atom = Assert.Single(ObserverAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        var target = Encoding.UTF8.GetBytes(Lean(gid));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var record = new ScribeEmissionRecord(
            gid,
            ScribeEmissionAttestation.DefinitionPath(gid),
            definitionHash,
            ScribeEmissionAttestation.EmissionPath(gid),
            emissionHash);
        var loaded = Ledger(
            atom,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed,
            gid,
            new DigestionCoverageEdge(
                gid,
                TestModuleStatementId),
            new DigestionScribeReceipt(gid, definitionHash, emissionHash),
            atomizer: AtomizerRegistry.ObserverId);
        var document = loaded.WithDigestionSources(
        [
            Assert.Single(loaded.RequireDigestionSources()) with
            {
                GenreRegistryProjection = GenreRegistryProjection.Available(
                    GenreRegistryCheck.Collected([token])),
            },
        ]);
        var snapshot = Snapshot([
            ("docs/source.md", source),
            CasFile(atom),
            (targetPath, target),
            (record.DefinitionPath, definition),
            (record.EmissionPath, emission),
            .. FrozenLedgerFiles(targetPath, "probe"),
        ]);

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            document,
            snapshot,
            AcceptedLean(targetPath),
            VerifiedScribeEmissions.Create([record]),
            baselineDocument: document).Entries);

        Assert.Equal(DigestionMigrationState.Absorbed, status.DerivedStatus.Migration);
        Assert.Equal(DigestionTruthState.Closed, status.DerivedStatus.Truth);
        var gap = Assert.Single(status.Gaps);
        Assert.Equal("unregistered-genre", gap.Code);
        Assert.Equal(token, gap.Detail);
        Assert.False(status.Deletable);
    }

    [Fact]
    public void StructuralRawSeenReplacesTheBoundaryPrerequisite()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        var document = StructuralLedger(atom);

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            document,
            Snapshot(("docs/source.md", source), CasFile(atom)),
            AcceptedLean(Array.Empty<string>()),
            baselineDocument: document).Entries);

        Assert.Equal(DigestionReceiptAlignment.Seen, status.Alignment);
        Assert.DoesNotContain(status.Gaps, gap => gap.Code == "normalized-seen-not-deletable");
    }

    [Fact]
    public void CasReceiptRemainsSeenAcrossNormalizedSourceRewrite()
    {
        var ledgerBytes = Encoding.UTF8.GetBytes(
            "# GICT\r\n\r\n**定理 1.1(Test)**。claim。\r\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(ledgerBytes, DigestionTestSupport.Rules).Claims);
        var document = StructuralLedger(atom);

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            document,
            Snapshot(("docs/source.md", currentBytes), CasFile(atom)),
            AcceptedLean(Array.Empty<string>()),
            baselineDocument: document).Entries);

        Assert.Equal(DigestionReceiptAlignment.Seen, status.Alignment);
        Assert.False(status.Deletable);
        Assert.DoesNotContain(status.Gaps, gap => gap.Code == "normalized-seen-not-deletable");
    }

    private static DigestionEntryEvaluation EvaluateDeclarationCoverage(
        string declarationGid,
        IEnumerable<string> describedDeclarations,
        bool includeCommittedEmission = true)
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        const string moduleGid = "D5/S0/Carrier/Probe";
        const string targetPath = "D5/S0/Carrier/Probe.lean";
        var target = Encoding.UTF8.GetBytes(Lean(moduleGid));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var record = new ScribeEmissionRecord(
            moduleGid,
            ScribeEmissionAttestation.DefinitionPath(moduleGid),
            definitionHash,
            ScribeEmissionAttestation.EmissionPath(moduleGid),
            emissionHash);
        var report = new LeanFileReport(
            ImmutableArray<string>.Empty,
            [new LeanDeclaration("probe", "theorem", "True", ImmutableArray<string>.Empty)
            {
                NameKey = "ns(n0,5:probe)",
            }]);
        var declarationStatementId = Assert.Single(
            CanonicalStatementWriter.DeclarationStatementIds(
                RepoPath.CreateKnown(targetPath),
                report)).StatementId.Value;
        var ledger = Ledger(
            atom,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed,
            declarationGid,
            new DigestionCoverageEdge(
                declarationGid,
                declarationStatementId),
            new DigestionScribeReceipt(declarationGid, definitionHash, emissionHash));
        var snapshotFiles = new List<(string Path, byte[] Bytes)>
        {
            ("docs/source.md", source),
            CasFile(atom),
            (targetPath, target),
            (ScribeEmissionAttestation.DefinitionPath(moduleGid), definition),
        };
        if (includeCommittedEmission)
        {
            snapshotFiles.Add((ScribeEmissionAttestation.EmissionPath(moduleGid), emission));
        }
        snapshotFiles.AddRange(FrozenLedgerFiles(
            targetPath,
            declarationGid[(declarationGid.LastIndexOf('.') + 1)..]));
        var snapshot = Snapshot([.. snapshotFiles]);

        return Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            ledger,
            snapshot,
            AcceptedLean((targetPath, report)),
            VerifiedScribeEmissions.Create([record], describedDeclarations)).Entries);
    }

    private static DigestionEntryEvaluation EvaluateCompleteTail(
        string authorizationPath,
        byte[] authorization,
        string? recordedSha256 = null,
        RawChangeSet? changes = null)
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        const string gid = "D5/X_Assumptions/Probe";
        const string targetPath = "D5/X_Assumptions/Probe.lean";
        var target = Encoding.UTF8.GetBytes(Lean(gid));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var ledger = Ledger(
            atom,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Tail,
            gid,
            new DigestionCoverageEdge(
                gid,
                TestModuleStatementId),
            new DigestionScribeReceipt(gid, definitionHash, emissionHash),
            tailAuthorization: new DigestionExternalReceipt(
                authorizationPath,
                recordedSha256 ?? DigestionFingerprint.Compute(authorization).RawSha256));
        var attestation = ScribeEmissionAttestation.Write(
        [
            new ScribeEmissionRecord(
                gid,
                ScribeEmissionAttestation.DefinitionPath(gid),
                definitionHash,
                ScribeEmissionAttestation.EmissionPath(gid),
                emissionHash),
        ]).ToArray();
        var report = new LeanFileReport(
            ImmutableArray<string>.Empty,
            [new LeanDeclaration("tailProbe", "axiom", "True", ["tailProbe"])]);
        var snapshot = Snapshot([
            ("docs/source.md", source),
            CasFile(atom),
            (targetPath, target),
            (ScribeEmissionAttestation.DefinitionPath(gid), definition),
            (ScribeEmissionAttestation.EmissionPath(gid), emission),
            (ScribeEmissionAttestation.RelativePath, attestation),
            (authorizationPath, authorization),
            .. FrozenLedgerFiles(targetPath, "tailProbe"),
        ]);

        var verifiedEmissions = VerifiedScribeEmissions.Create(
        [
            new ScribeEmissionRecord(
                gid,
                ScribeEmissionAttestation.DefinitionPath(gid),
                definitionHash,
                ScribeEmissionAttestation.EmissionPath(gid),
                emissionHash),
        ]);
        return Assert.Single(DigestionStatusEvaluator.Evaluate(
            changes is null
                ? DigestionEvaluationScope.FullScan
                : DigestionEvaluationScope.ChangedSet,
            ledger,
            snapshot,
            AcceptedLean((targetPath, report)),
            verifiedEmissions,
            changes: changes).Entries);
    }

    private static string CompleteTailAtomId() =>
        Assert.Single(GictAtomizer.Atomize(
            Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n"),
            DigestionTestSupport.Rules).Claims)
        .Fingerprints.RawSha256["sha256:".Length..];

    private static BackfillInventoryDocument Ledger(
        DigestionAtom atom,
        DigestionMigrationState migration,
        DigestionTruthState truth,
        string coverageGid = "D5/X_Frontier/Probe",
        DigestionCoverageEdge? coverageReceipt = null,
        DigestionScribeReceipt? scribeReceipt = null,
        string atomizer = AtomizerRegistry.GictId,
        bool includeCoverageGid = true,
        DigestionExternalReceipt? tailAuthorization = null)
    {
        var receipts = new DigestionReceipts(
            scribeReceipt is null ? [] : [scribeReceipt],
            [],
            [],
            tailAuthorization);
        var entry = DigestionTestSupport.Entry(
            atom,
            atom.Fingerprints.RawSha256["sha256:".Length..],
            atomizer,
            migration,
            truth,
            [],
            receipts,
            AtomizerRegistry.GictId) with
        {
            Coverage = coverageReceipt is not null
                ? [coverageReceipt]
                : includeCoverageGid
                    ? [new DigestionCoverageEdge(coverageGid, null)]
                    : [],
        };
        return DigestionTestSupport.Document(
            atomizer,
            [entry],
            AtomizerRegistry.GictId);
    }

    private static readonly string TestModuleStatementId =
        FrozenStatementReceiptTestData.Id('a');

    private static readonly string TestDeclarationStatementId =
        FrozenStatementReceiptTestData.Id('b');

    private static (string Path, byte[] Bytes)[] FrozenLedgerFiles(
        string modulePath,
        params string[] declarationSelectors) =>
        FrozenStatementReceiptTestData.LedgerFiles(
            new FrozenStatementReceiptTestData.Module(
                modulePath,
                TestModuleStatementId,
                declarationSelectors.Select(selector =>
                    new FrozenStatementReceiptTestData.Declaration(
                        selector,
                        TestDeclarationStatementId))
                    .ToImmutableArray()));

    private static BackfillInventoryDocument StructuralLedger(DigestionAtom atom)
    {
        var document = Ledger(
            atom,
            DigestionMigrationState.Residual,
            DigestionTruthState.Open,
            includeCoverageGid: false);
        var source = Assert.Single(document.RequireDigestionSources());
        return document.WithDigestionSources(
        [
            source with
            {
                GenreRegistryProjection = GenreRegistryProjection.Available(
                    GenreRegistryCheck.Collected([])),
            },
        ]);
    }

}
