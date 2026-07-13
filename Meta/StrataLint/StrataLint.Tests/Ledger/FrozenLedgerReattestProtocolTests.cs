using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    private const string OriginalReattestSource = "theorem a : True := by trivial\n";
    private const string ChangedHeaderReattestSource =
        "-- canonical header changed\ntheorem a : True := by trivial\n";

    [Fact]
    public void ExtendedReattestUpdatesBlobWhilePreservingStatementIdentity()
    {
        var baselineCatalog = BuildCatalog(Module("A", source: OriginalReattestSource));
        var candidateCatalog = BuildCatalog(Module("A", source: ChangedHeaderReattestSource));
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            baselineCatalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baselineSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(baselineBytes.AsSpan())).Syntax;
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(baselineSyntax, baselineCatalog)).Capability;

        var candidateBytes = FrozenLedgerGenerator.AppendReattestation(baseline, candidateCatalog);
        var candidateSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(candidateBytes.AsSpan())).Syntax;
        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateCandidate(candidateSyntax, baseline, candidateCatalog)).Capability;
        var history = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(candidateSyntax, candidateCatalog)).Capability;
        var reattest = Assert.IsType<FrozenLedgerEvent.Reattest>(accepted.Events[^1]);
        var baselineNode = baselineCatalog.ClosedNodes.Single();
        var candidateNode = candidateCatalog.ClosedNodes.Single();

        Assert.True(candidateBytes.AsSpan().StartsWith(baselineBytes.AsSpan()));
        Assert.Equal(baselineNode.StatementId, candidateNode.StatementId);
        Assert.NotEqual(baselineNode.FrozenNodeId, candidateNode.FrozenNodeId);
        Assert.Equal(candidateNode.FrozenNodeId, reattest.Payload.FrozenNodeId);
        Assert.Equal(candidateNode.Attestation.SourceBlobOid, reattest.Payload.Input.DescriptorBlobOid);
        Assert.Equal(candidateNode.FrozenNodeId, history.ActiveFrozenNodes.Single().FrozenNodeId);
    }

    [Fact]
    public void ExtendedReattestIsIdempotentOnceCandidateMaterialIsActive()
    {
        var baselineCatalog = BuildCatalog(Module("A", source: OriginalReattestSource));
        var candidateCatalog = BuildCatalog(Module("A", source: ChangedHeaderReattestSource));
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            baselineCatalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(
                    DagLedgerLoader.Load(baselineBytes.AsSpan())).Syntax,
                baselineCatalog)).Capability;
        var firstBytes = FrozenLedgerGenerator.AppendReattestation(baseline, candidateCatalog);
        var first = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateCandidate(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(
                    DagLedgerLoader.Load(firstBytes.AsSpan())).Syntax,
                baseline,
                candidateCatalog)).Capability;

        var secondBytes = FrozenLedgerGenerator.AppendReattestation(first, candidateCatalog);

        Assert.True(secondBytes.AsSpan().SequenceEqual(firstBytes.AsSpan()));
    }

    [Fact]
    public void ExtendedReattestCannotChangeStatementIdentity()
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
            freeze.Payload.DeclarationStatementIds,
            freeze.Payload.FrozenNodeId,
            freeze.Payload.Input,
            freeze.Payload.InputFingerprint,
            freeze.Payload.PrerequisiteFrozenNodeIds,
            freeze.EventHash,
            freeze.Payload.SemanticReceipt,
            StatementId.Create(Sha256("different-statement")),
            freeze.Payload.WitnessId);
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

        Assert.Contains("statement identity", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void HistoryPrefixAllowsSameStatementBlobToAwaitReattestation()
    {
        var baselineCatalog = BuildCatalog(Module("A", source: OriginalReattestSource));
        var candidateCatalog = BuildCatalog(Module("A", source: ChangedHeaderReattestSource));
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            baselineCatalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(baselineBytes.AsSpan())).Syntax;

        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            FrozenLedger.ValidateHistoryPrefix(syntax, candidateCatalog, Trust(syntax))).Capability;

        Assert.Equal(baselineCatalog.ClosedNodes.Single().FrozenNodeId,
            accepted.ActiveFrozenNodes.Single().FrozenNodeId);
    }

    [Fact]
    public void HistoricalValidationPreservesGenesisRuleCatalogAcrossCatalogEvolution()
    {
        var catalog = BuildCatalog(Module("A"));
        var historicalRoot = Sha256("historical-rule-catalog");
        Assert.NotEqual(RuleCatalog.Default.RootSha256, historicalRoot);
        var bytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), historicalRoot));
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(bytes.AsSpan())).Syntax;

        var newGenesis = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateGenesis(syntax, catalog));
        var history = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(syntax, catalog)).Capability;

        Assert.Contains("catalog", newGenesis.Message, StringComparison.OrdinalIgnoreCase);
        var genesis = Assert.IsType<FrozenLedgerEvent.Genesis>(history.Events[0]);
        Assert.Equal(historicalRoot, genesis.Payload.RuleCatalogRoot);
    }
}
