using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void ProductionValidatorRejectsWhenEitherLedgerIsMissing(bool removeBaselineLedger)
    {
        var fixture = CreateFrozenValidatorFixture();
        var files = removeBaselineLedger ? fixture.BaselineFiles : fixture.CurrentFiles;
        files.Remove(FrozenLedgerChangeClassifier.LedgerPath);
        var gateway = CreateGateway(fixture);

        var outcome = Validate(fixture, gateway);

        AssertSl008Rejection(
            outcome,
            "frozen ledger is missing from current or protected baseline");
        Assert.Equal(0, gateway.FrozenReferenceValidationCount);
    }

    [Theory]
    [InlineData(true, "protected baseline ledger syntax is invalid: Frozen ledger contains a blank or CR-terminated line.")]
    [InlineData(false, "candidate ledger syntax is invalid: Frozen ledger contains a blank or CR-terminated line.")]
    public void ProductionValidatorRejectsInvalidLedgerSyntax(
        bool corruptBaselineLedger,
        string expectedMessage)
    {
        var fixture = CreateFrozenValidatorFixture();
        var files = corruptBaselineLedger ? fixture.BaselineFiles : fixture.CurrentFiles;
        files[FrozenLedgerChangeClassifier.LedgerPath] = "\n";
        var gateway = CreateGateway(fixture);

        var outcome = Validate(fixture, gateway);

        AssertSl008Rejection(outcome, expectedMessage);
        Assert.Equal(0, gateway.FrozenReferenceValidationCount);
    }

    [Theory]
    [InlineData(true, "protected baseline ledger fields are invalid: event envelope has unknown, missing, or duplicate fields.")]
    [InlineData(false, "candidate ledger fields are invalid: event envelope has unknown, missing, or duplicate fields.")]
    public void ProductionValidatorRejectsInvalidLedgerFields(
        bool corruptBaselineLedger,
        string expectedMessage)
    {
        var fixture = CreateFrozenValidatorFixture();
        var files = corruptBaselineLedger ? fixture.BaselineFiles : fixture.CurrentFiles;
        files[FrozenLedgerChangeClassifier.LedgerPath] = "{}\n";
        var gateway = CreateGateway(fixture);

        var outcome = Validate(fixture, gateway);

        AssertSl008Rejection(outcome, expectedMessage);
        Assert.Equal(0, gateway.FrozenReferenceValidationCount);
    }

    [Fact]
    public void ProductionValidatorAcceptsARevocationBackedByAProtectedTypedReceipt()
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
        var baselineReports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
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
        var baselineState = BuildState(baselineFiles, baselineReports);
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
        var genesisBytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(
                FrozenLedgerTestData.GitOid('e'),
                RuleCatalog.Default.RootSha256));
        var genesis = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            FrozenLedgerTestData.ValidateGenesis(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(
                    DagLedgerLoader.Load(genesisBytes.AsSpan())).Syntax,
                catalog)).Capability;
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
        const string receiptPath = "Evidence/D5/revocation-receipt.json";
        baselineFiles[receiptPath] = receiptText;
        var protectedSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(Snapshot(baselineFiles))).Snapshot;
        var receipts = Assert.IsType<RevocationReceiptStoreOutcome.Accepted>(
            TrustedRevocationReceiptStore.Materialize(
                genesis,
                protectedSnapshot,
                new[] { receiptOid })).Capability;
        var validatedEvidence = Assert.IsType<RevocationEvidenceValidationOutcome.Accepted>(
            RevocationEvidenceValidator.Validate(evidence, genesis, receipts)).Capability;
        var plan = Assert.IsType<RevocationPlanOutcome.Accepted>(
            RevocationPlanner.Plan(genesis, new[] { validatedEvidence })).Capability;
        var candidateBytes = FrozenLedgerGenerator.AppendRevocation(genesis, plan);
        baselineFiles[FrozenLedgerChangeClassifier.LedgerPath] = Encoding.UTF8.GetString(genesisBytes.AsSpan());
        var currentFiles = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["lean-toolchain"] = toolchain,
            ["lake-manifest.json"] = manifest,
            [receiptPath] = receiptText,
            [FrozenLedgerChangeClassifier.LedgerPath] = Encoding.UTF8.GetString(candidateBytes.AsSpan()),
        };
        var finalBaseline = BuildState(baselineFiles, baselineReports);
        var current = BuildState(
            currentFiles,
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal));

        var rejection = ProductionFrozenLedgerValidator.Validate(
            current.Snapshot,
            finalBaseline.Snapshot,
            current.Lean,
            finalBaseline.Lean,
            current.Dag,
            finalBaseline.Dag,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(currentFiles),
                Snapshot(baselineFiles)));

        Assert.True(
            rejection is null,
            rejection is AdmissionOutcome.RuleRejected rejected
                ? string.Join(" | ", rejected.Diagnostics.Select(static item => item.Message))
                : rejection?.ToString());
    }

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

    private static FakeRepositoryGateway CreateGateway(FrozenValidatorFixture fixture) =>
        new(
            RawChangeSet.Create(Array.Empty<string>()),
            Snapshot(fixture.CurrentFiles),
            Snapshot(fixture.BaselineFiles));

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
        Dictionary<string, LeanFileReport> CurrentReports);
}
