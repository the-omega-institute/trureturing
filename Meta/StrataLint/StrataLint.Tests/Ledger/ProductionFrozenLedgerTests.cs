using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void BaselineLedgerResolutionAcceptsAUniqueByteExactRelocation()
    {
        const string previousPath = "Meta/StrataLint/Golden/Frozen/events.jsonl";
        const string bytes = "{\"schema\":\"fixture\"}\n";
        var baseline = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(Snapshot(new Dictionary<string, string>(StringComparer.Ordinal)
            {
                [previousPath] = bytes,
            }))).Snapshot;
        var current = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(Snapshot(new Dictionary<string, string>(StringComparer.Ordinal)
            {
                [FrozenLedgerChangeClassifier.LedgerPath] = bytes,
            }))).Snapshot;
        Assert.True(current.TryGetFile(FrozenLedgerChangeClassifier.LedgerPath, out var currentFile));

        var resolved = ProductionFrozenLedgerValidator.ResolveBaselineLedger(
            baseline,
            currentFile);

        Assert.NotNull(resolved);
        Assert.Equal(previousPath, resolved.Path.Value);
    }

    [Fact]
    public void BaselineLedgerResolutionAcceptsAnExplicitHistoricalCurrentPath()
    {
        const string historicalPath = "Archive/Frozen/events.jsonl";
        const string bytes = "{\"schema\":\"fixture\"}\n";
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(Snapshot(new Dictionary<string, string>(StringComparer.Ordinal)
            {
                [historicalPath] = bytes,
            }))).Snapshot;
        Assert.True(snapshot.TryGetFile(historicalPath, out var currentFile));

        var resolved = ProductionFrozenLedgerValidator.ResolveBaselineLedger(
            snapshot,
            currentFile,
            historicalPath);

        Assert.NotNull(resolved);
        Assert.Equal(historicalPath, resolved.Path.Value);
    }

    [Fact]
    public void BaselineLedgerResolutionRejectsAChangedRelocation()
    {
        const string previousPath = "Meta/StrataLint/Golden/Frozen/events.jsonl";
        var baseline = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(Snapshot(new Dictionary<string, string>(StringComparer.Ordinal)
            {
                [previousPath] = "baseline\n",
            }))).Snapshot;
        var current = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(Snapshot(new Dictionary<string, string>(StringComparer.Ordinal)
            {
                [FrozenLedgerChangeClassifier.LedgerPath] = "candidate\n",
            }))).Snapshot;
        Assert.True(current.TryGetFile(FrozenLedgerChangeClassifier.LedgerPath, out var currentFile));

        Assert.Null(ProductionFrozenLedgerValidator.ResolveBaselineLedger(baseline, currentFile));
    }

    [Fact]
    public void BaselineLedgerResolutionRejectsAmbiguousByteExactRelocations()
    {
        const string bytes = "{\"schema\":\"fixture\"}\n";
        var baseline = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(Snapshot(new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["First/Frozen/events.jsonl"] = bytes,
                ["Second/Frozen/events.jsonl"] = bytes,
            }))).Snapshot;
        var current = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(Snapshot(new Dictionary<string, string>(StringComparer.Ordinal)
            {
                [FrozenLedgerChangeClassifier.LedgerPath] = bytes,
            }))).Snapshot;
        Assert.True(current.TryGetFile(FrozenLedgerChangeClassifier.LedgerPath, out var currentFile));

        Assert.Null(ProductionFrozenLedgerValidator.ResolveBaselineLedger(baseline, currentFile));
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
}
