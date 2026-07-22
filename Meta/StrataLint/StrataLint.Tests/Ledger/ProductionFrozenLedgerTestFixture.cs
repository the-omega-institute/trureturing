using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    private static FrozenValidatorFixture CreateFrozenValidatorFixture()
    {
        const string path = "D5/S0/Carrier/A.lean";
        const string source = "theorem a : True := by trivial\n";
        const string toolchain = "leanprover/lean4:v4.24.0\n";
        const string manifest = "{}\n";
        var baselineFiles = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [path] = source,
            ["lean-toolchain"] = toolchain,
            ["lake-manifest.json"] = manifest,
        };
        var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
        {
            [path] = new(
                ImmutableArray<string>.Empty,
                ImmutableArray.Create(new LeanDeclaration(
                    "a",
                    "theorem",
                    "True",
                    ImmutableArray<string>.Empty)
                {
                    NameKey = "ns(n0,1:a)",
                })),
        };
        var baselineState = BuildState(baselineFiles, reports);
        var environment = new FrozenEnvironmentAttestation(
            FrozenLedgerTestData.GitOid('a'),
            FrozenLedgerTestData.GitOid('b'),
            FrozenLedgerTestData.GitBlobOid(toolchain),
            FrozenLedgerTestData.GitBlobOid(manifest));
        var catalog = Assert.IsType<FrozenMaterialOutcome.Accepted>(FrozenContentAddress.Build(
            baselineState.Snapshot,
            baselineState.Lean,
            baselineState.Dag,
            environment,
            new[]
            {
                new FrozenModuleAttestation(
                    RepoPath.CreateKnown(path),
                    FrozenLedgerTestData.GitBlobOid(source)),
            })).Capability;
        var ledger = Encoding.UTF8.GetString(FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(
                FrozenLedgerTestData.GitOid('e'),
                RuleCatalog.Default.RootSha256)).AsSpan());
        baselineFiles[FrozenLedgerChangeClassifier.LedgerPath] = ledger;
        return new FrozenValidatorFixture(
            baselineFiles,
            new Dictionary<string, string>(baselineFiles, StringComparer.Ordinal),
            reports,
            new Dictionary<string, LeanFileReport>(reports, StringComparer.Ordinal));
    }

    private static FrozenValidatorFixture CreateRevocationValidatorFixture(bool includeReceiptInBaseline)
    {
        const string receiptPath = "Evidence/D5/revocation-receipt.json";
        var fixture = CreateFrozenValidatorFixture();
        var baseline = BuildState(fixture.BaselineFiles, fixture.BaselineReports);
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(
            Encoding.UTF8.GetBytes(fixture.BaselineFiles[FrozenLedgerChangeClassifier.LedgerPath]))).Syntax;
        var references = Assert.IsType<FrozenLedgerReferenceScanOutcome.Accepted>(
            FrozenLedger.ScanReferences(syntax)).References;
        var catalog = Assert.IsType<FrozenMaterialOutcome.Accepted>(FrozenLedgerMaterializer.Build(
            baseline.Snapshot,
            baseline.Lean,
            baseline.Dag,
            syntax)).Capability;
        var genesis = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(FrozenLedger.ValidateHistory(
            syntax,
            catalog,
            TrustedFrozenGitReferences.CreateForTrustedAdapter(references.Inputs))).Capability;
        var node = Assert.Single(genesis.ActiveFrozenNodes);
        var provisional = new RevocationEvidence.KernelWitnessFailure(
            node.FrozenNodeId,
            node.WitnessId,
            string.Empty,
            string.Empty);
        var receiptBytes = RevocationReceiptWriter.Write(genesis, provisional);
        var receiptText = Encoding.UTF8.GetString(receiptBytes.AsSpan());
        var receiptOid = FrozenLedgerTestData.GitBlobOid(receiptText);
        var evidence = provisional with
        {
            ReceiptBlobOid = receiptOid,
            ReceiptSha256 = FrozenLedgerTestData.Sha256(receiptText),
        };
        var receiptFiles = new Dictionary<string, string>(fixture.BaselineFiles, StringComparer.Ordinal)
        {
            [receiptPath] = receiptText,
        };
        var protectedSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(Snapshot(receiptFiles))).Snapshot;
        var receipts = Assert.IsType<RevocationReceiptStoreOutcome.Accepted>(
            TrustedRevocationReceiptStore.Materialize(
                genesis,
                protectedSnapshot,
                new[] { receiptOid })).Capability;
        var validatedEvidence = Assert.IsType<RevocationEvidenceValidationOutcome.Accepted>(
            RevocationEvidenceValidator.Validate(evidence, genesis, receipts)).Capability;
        var plan = Assert.IsType<RevocationPlanOutcome.Accepted>(
            RevocationPlanner.Plan(genesis, new[] { validatedEvidence })).Capability;
        if (includeReceiptInBaseline)
        {
            fixture.BaselineFiles[receiptPath] = receiptText;
        }

        fixture.CurrentFiles.Clear();
        fixture.CurrentFiles["lean-toolchain"] = fixture.BaselineFiles["lean-toolchain"];
        fixture.CurrentFiles["lake-manifest.json"] = fixture.BaselineFiles["lake-manifest.json"];
        fixture.CurrentFiles[receiptPath] = receiptText;
        fixture.CurrentFiles[FrozenLedgerChangeClassifier.LedgerPath] = Encoding.UTF8.GetString(
            FrozenLedgerGenerator.AppendRevocation(genesis, plan).AsSpan());
        fixture.CurrentReports.Clear();
        return fixture with { ReceiptOid = receiptOid };
    }

    private static void AppendCurrentReattestation(FrozenValidatorFixture fixture)
    {
        var baseline = BuildState(fixture.BaselineFiles, fixture.BaselineReports);
        var ledgerFile = fixture.BaselineFiles[FrozenLedgerChangeClassifier.LedgerPath];
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(Encoding.UTF8.GetBytes(ledgerFile))).Syntax;
        var references = Assert.IsType<FrozenLedgerReferenceScanOutcome.Accepted>(
            FrozenLedger.ScanReferences(syntax)).References;
        var catalog = Assert.IsType<FrozenMaterialOutcome.Accepted>(FrozenLedgerMaterializer.Build(
            baseline.Snapshot,
            baseline.Lean,
            baseline.Dag,
            syntax)).Capability;
        var history = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(FrozenLedger.ValidateHistory(
            syntax,
            catalog,
            TrustedFrozenGitReferences.CreateForTrustedAdapter(references.Inputs))).Capability;
        fixture.CurrentFiles[FrozenLedgerChangeClassifier.LedgerPath] = Encoding.UTF8.GetString(
            FrozenLedgerGenerator.AppendReattestation(
                history,
                Assert.Single(history.ActiveEntries).Key,
                Assert.Single(references.Inputs)).AsSpan());
    }

    private static FakeRepositoryGateway CreateGateway(
        FrozenValidatorFixture fixture,
        Func<FrozenLedgerReferenceSet, TrustedFrozenGitReferences>? frozenReferenceValidator = null) =>
        new(
            RawChangeSet.Create(Array.Empty<string>()),
            Snapshot(fixture.CurrentFiles),
            Snapshot(fixture.BaselineFiles),
            frozenReferenceValidator);

    private static AdmissionOutcome? Validate(
        FrozenValidatorFixture fixture,
        FakeRepositoryGateway gateway)
    {
        var current = BuildState(fixture.CurrentFiles, fixture.CurrentReports);
        var baseline = BuildState(fixture.BaselineFiles, fixture.BaselineReports);
        return ProductionFrozenLedgerValidator.Validate(
            current.Snapshot,
            baseline.Snapshot,
            current.Lean,
            baseline.Lean,
            current.Dag,
            baseline.Dag,
            gateway);
    }

    private static void AssertSl008Rejection(AdmissionOutcome? outcome, string expectedMessage)
    {
        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var diagnostic = Assert.Single(rejected.Diagnostics);
        Assert.Equal(RuleId.CreateKnown(8), diagnostic.RuleId);
        Assert.Equal("Frozen Hearts semantics", diagnostic.Title);
        Assert.Equal(DisplaySeverity.Error, diagnostic.DisplaySeverity);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Equal(FrozenLedgerChangeClassifier.LedgerPath, diagnostic.Path);
        Assert.Equal(expectedMessage, diagnostic.Message);
        Assert.Equal($"SL-008 {FrozenLedgerChangeClassifier.LedgerPath}: {expectedMessage}", diagnostic.Render());
    }

    private sealed record FrozenValidatorFixture(
        Dictionary<string, string> BaselineFiles,
        Dictionary<string, string> CurrentFiles,
        Dictionary<string, LeanFileReport> BaselineReports,
        Dictionary<string, LeanFileReport> CurrentReports,
        string? ReceiptOid = null);
}
