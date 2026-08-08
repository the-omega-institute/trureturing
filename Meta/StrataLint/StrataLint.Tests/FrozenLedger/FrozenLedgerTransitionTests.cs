using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Fact]
    public void FreezeOfAnOpenNodeFailsEvenWithAValidCaseAndEventHash()
    {
        const string pathText = "D5/X_Frontier/OpenCase.lean";
        const string source = "-- D5-T0042\ntheorem openCase : True := by sorry\n";
        var catalog = Assert.IsType<FrozenMaterialOutcome.Accepted>(BuildCatalogOutcome(
            pathText,
            source,
            new LeanFileReport(
                ImmutableArray<string>.Empty,
                ImmutableArray.Create(new LeanDeclaration(
                    "openCase",
                    "theorem",
                    "True",
                    ImmutableArray.Create("sorryAx")))))).Capability;
        var genesisBytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var genesis = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(genesisBytes.AsSpan())).Syntax,
                catalog)).Capability;
        Assert.True(RepoPath.TryCreate(pathText, out var path));
        var statement = StatementId.Create(Sha256("statement"));
        var witness = WitnessId.Create(Sha256("witness"));
        var frozen = FrozenNodeId.Create(Sha256("frozen"));
        var payload = new FrozenFreezePayload(
            "active-frozen",
            "active-frozen/" + frozen.Value[7..],
            ImmutableArray<FrozenDeclarationStatement>.Empty,
            "admission",
            new FrozenExpectedVerdict(
                ImmutableArray.Create("admit"),
                "none",
                ImmutableArray<FrozenExpectedDiagnostic>.Empty),
            frozen,
            new FrozenLedgerInput(
                catalog.Environment.OriginCommitOid,
                catalog.Environment.OriginTreeOid,
                GitBlobOid(source),
                pathText,
                "repository-snapshot-v1",
                new[]
                {
                    catalog.Environment.LakeManifestBlobOid,
                    catalog.Environment.LeanToolchainBlobOid,
                }.Order(StringComparer.Ordinal).ToImmutableArray()),
            witness.Value,
            path,
            ImmutableArray<FrozenNodeId>.Empty,
            frozen.Value,
            statement,
            nameof(TruthState.Closed),
            witness);
        var line = FrozenLedgerCanonicalWriter.WriteEvent(
            "Freeze",
            FrozenLedgerCanonicalWriter.FreezeElement(payload),
            genesis.HeadHash,
            1).Bytes;
        var forged = genesisBytes.Concat(line).ToArray();

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateGenesis(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(forged)).Syntax,
                catalog));

        Assert.Contains("outside the current Closed catalog", rejected.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ReattestCannotChangeSemanticReceipt()
    {
        var catalog = BuildCatalog(Module("A"));
        var bytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes.AsSpan())).Syntax,
                catalog)).Capability;
        var freeze = Assert.IsType<FrozenLedgerEvent.Freeze>(baseline.Events[1]);
        var forged = new FrozenReattestPayload(
            freeze.Payload.CaseId,
            freeze.Payload.Input,
            freeze.Payload.InputFingerprint,
            freeze.EventHash,
            Sha256("different-semantic-receipt"));
        var line = FrozenLedgerCanonicalWriter.WriteEvent(
            "Reattest",
            FrozenLedgerCanonicalWriter.ReattestElement(forged),
            baseline.HeadHash,
            baseline.Events.Length).Bytes;

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(
                    DagLedgerLoader.Load(bytes.Concat(line).ToArray())).Syntax,
                baseline,
                catalog));

        Assert.Contains("semantic identity", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ReattestCannotSwapDescriptorBytesWhileEchoingTheOldFingerprint()
    {
        var catalog = BuildCatalog(Module("A"));
        var bytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes.AsSpan())).Syntax,
                catalog)).Capability;
        var freeze = Assert.IsType<FrozenLedgerEvent.Freeze>(baseline.Events[1]);
        var forged = new FrozenReattestPayload(
            freeze.Payload.CaseId,
            freeze.Payload.Input with { DescriptorBlobOid = GitOid('f') },
            freeze.Payload.InputFingerprint,
            freeze.EventHash,
            freeze.Payload.SemanticReceipt);
        var line = FrozenLedgerCanonicalWriter.WriteEvent(
            "Reattest",
            FrozenLedgerCanonicalWriter.ReattestElement(forged),
            baseline.HeadHash,
            baseline.Events.Length).Bytes;

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(
                    DagLedgerLoader.Load(bytes.Concat(line).ToArray())).Syntax,
                baseline,
                catalog));

        Assert.Contains("attestation", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }
}
