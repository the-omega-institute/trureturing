using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Nodes;
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
    public void ExtendedReattestRejectsAxiomClosureThatDisagreesWithCandidateReport()
    {
        var baselineCatalog = BuildCatalog(Module(
            "A",
            source: OriginalReattestSource,
            axioms: new[] { "Classical.choice" }));
        var candidateCatalog = BuildCatalog(Module(
            "A",
            source: ChangedHeaderReattestSource,
            axioms: new[] { "Classical.choice" }));
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            baselineCatalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(
                    DagLedgerLoader.Load(baselineBytes.AsSpan())).Syntax,
                baselineCatalog)).Capability;
        var generatedBytes = FrozenLedgerGenerator.AppendReattestation(baseline, candidateCatalog);
        var generatedSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(generatedBytes.AsSpan())).Syntax;
        var generatedPayload = generatedSyntax.Lines[^1].Value.GetProperty("payload");
        Assert.Equal(
            candidateCatalog.ClosedNodes.Single().AxiomClosure,
            generatedPayload.GetProperty("axiom_closure")
                .EnumerateArray()
                .Select(static item => item.GetString()!));
        var forgedPayload = JsonNode.Parse(generatedPayload.GetRawText())!.AsObject();
        forgedPayload["axiom_closure"] = new JsonArray("propext");
        var forgedLine = FrozenLedgerCanonicalWriter.WriteEvent(
            "Reattest",
            JsonSerializer.SerializeToElement(forgedPayload),
            baseline.HeadHash,
            baseline.Events.Length).Bytes;
        var forgedSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(baselineBytes.Concat(forgedLine).ToArray())).Syntax;

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(forgedSyntax, baseline, candidateCatalog));

        Assert.Contains("recomputed material", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ClosureOnlyReattestRejectsAxiomClosureThatDisagreesWithCandidateReport()
    {
        var catalog = BuildCatalog(Module("A", axioms: new[] { "Classical.choice" }));
        var generated = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var legacyBytes = WithoutRecordedAxiomClosures(generated);
        var legacySyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(legacyBytes.AsSpan())).Syntax;
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            FrozenLedger.ValidateHistoryPrefix(legacySyntax, catalog, Trust(legacySyntax))).Capability;
        var candidateBytes = FrozenLedgerGenerator.AppendReattestation(baseline, catalog);
        var candidateSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(candidateBytes.AsSpan())).Syntax;
        var payload = JsonNode.Parse(
            candidateSyntax.Lines[^1].Value.GetProperty("payload").GetRawText())!.AsObject();
        Assert.False(payload.ContainsKey("declaration_statement_ids"));
        payload["axiom_closure"] = new JsonArray("propext");
        var forgedLine = FrozenLedgerCanonicalWriter.WriteEvent(
            "Reattest",
            JsonSerializer.SerializeToElement(payload),
            baseline.HeadHash,
            baseline.Events.Length).Bytes;
        var forgedSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(legacyBytes.Concat(forgedLine).ToArray())).Syntax;

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(forgedSyntax, baseline, catalog));

        Assert.Contains("recomputed material", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void AppendReattestationBackfillsUnknownClosureWithoutMaterialDrift()
    {
        var catalog = BuildCatalog(Module("A", axioms: new[] { "Classical.choice" }));
        var generated = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var legacyBytes = WithoutRecordedAxiomClosures(generated);
        var legacySyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(legacyBytes.AsSpan())).Syntax;
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            FrozenLedger.ValidateHistoryPrefix(legacySyntax, catalog, Trust(legacySyntax))).Capability;
        Assert.False(baseline.ActiveEntries.Values.Single().AxiomClosureKnown);

        var candidateBytes = FrozenLedgerGenerator.AppendReattestation(baseline, catalog);
        var candidate = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateCandidate(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(
                    DagLedgerLoader.Load(candidateBytes.AsSpan())).Syntax,
                baseline,
                catalog)).Capability;

        var reattest = Assert.IsType<FrozenLedgerEvent.Reattest>(candidate.Events[^1]);
        Assert.Equal(baseline.Events.Length + 1, candidate.Events.Length);
        Assert.Equal(baseline.ActiveEntries.Values.Single().Payload.CaseId, reattest.Payload.CaseId);
        Assert.Equal(
            catalog.ClosedNodes.Single().AxiomClosure,
            Assert.IsType<DagLedgerLoadOutcome.Loaded>(
                DagLedgerLoader.Load(candidateBytes.AsSpan())).Syntax.Lines[^1].Value
                .GetProperty("payload")
                .GetProperty("axiom_closure")
                .EnumerateArray()
                .Select(static item => item.GetString()!));
        Assert.True(candidate.ActiveEntries.Values.Single().AxiomClosureKnown);
    }

    [Fact]
    public void AppendSynchronizationAtomicallyReattestsRepresentationDriftAndFreezesNewModules()
    {
        var baselineCatalog = BuildCatalog(
            Module("A", source: OriginalReattestSource),
            Module("C", imports: new[] { "A" }));
        var candidateCatalog = BuildCatalog(
            Module("A", source: ChangedHeaderReattestSource),
            Module("B", imports: new[] { "A" }),
            Module("C", imports: new[] { "A" }));
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            baselineCatalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baselineSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(baselineBytes.AsSpan())).Syntax;
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(baselineSyntax, baselineCatalog)).Capability;

        var candidateBytes = FrozenLedgerGenerator.AppendSynchronization(baseline, candidateCatalog);
        var candidateSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(candidateBytes.AsSpan())).Syntax;
        var candidate = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateCandidate(candidateSyntax, baseline, candidateCatalog)).Capability;
        var history = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(candidateSyntax, candidateCatalog)).Capability;

        Assert.True(candidateBytes.AsSpan().StartsWith(baselineBytes.AsSpan()));
        Assert.Equal(
            new[] { "Reattest", "Reattest", "Freeze" },
            candidateSyntax.Lines
                .Skip(baseline.Events.Length)
                .Select(static line => line.Value.GetProperty("event_type").GetString()));
        Assert.Equal(2, candidate.Events.OfType<FrozenLedgerEvent.Reattest>().Count());
        Assert.Equal(3, candidate.ActiveFrozenNodes.Length);
        Assert.Equal(3, history.ActiveFrozenNodes.Length);
    }

    [Fact]
    public void AppendSynchronizationDirectsStatementIdentityChangesToRevoke()
    {
        var baselineCatalog = BuildCatalog(ModuleWithReport(
            "A",
            OriginalReattestSource,
            "True",
            declarations: new[] { "a" }));
        var candidateCatalog = BuildCatalog(ModuleWithReport(
            "A",
            OriginalReattestSource,
            "False",
            declarations: new[] { "a" }));
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            baselineCatalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(
                    DagLedgerLoader.Load(baselineBytes.AsSpan())).Syntax,
                baselineCatalog)).Capability;

        var exception = Assert.Throws<InvalidOperationException>(
            () => FrozenLedgerGenerator.AppendSynchronization(baseline, candidateCatalog));

        Assert.Contains(PathFor("A"), exception.Message, StringComparison.Ordinal);
        Assert.Contains("statement identity", exception.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("Revoke", exception.Message, StringComparison.Ordinal);
        Assert.DoesNotContain("ledger-supersede", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AppendSynchronizationDirectsAnActiveModuleThatIsNoLongerClosedToRevoke()
    {
        var baselineCatalog = BuildCatalog(Module("A"));
        var candidateCatalog = BuildCatalog(Module("B"));
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            baselineCatalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(
                    DagLedgerLoader.Load(baselineBytes.AsSpan())).Syntax,
                baselineCatalog)).Capability;

        var exception = Assert.Throws<InvalidOperationException>(
            () => FrozenLedgerGenerator.AppendSynchronization(baseline, candidateCatalog));

        Assert.Contains(PathFor("A"), exception.Message, StringComparison.Ordinal);
        Assert.Contains("no longer Closed", exception.Message, StringComparison.Ordinal);
        Assert.Contains("Revoke", exception.Message, StringComparison.Ordinal);
        Assert.Contains("ledger-sync", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AppendSynchronizationReattestsDriftWhenNoFreezeIsMissing()
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

        var candidateBytes = FrozenLedgerGenerator.AppendSynchronization(baseline, candidateCatalog);
        var candidateSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(candidateBytes.AsSpan())).Syntax;
        var candidate = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateCandidate(candidateSyntax, baseline, candidateCatalog)).Capability;

        var appended = Assert.IsType<FrozenLedgerEvent.Reattest>(candidate.Events[^1]);
        Assert.Equal(PathFor("A"), appended.Payload.Input.DescriptorSelector);
        Assert.Equal(baseline.Events.Length + 1, candidate.Events.Length);
    }

    [Fact]
    public void AppendSynchronizationIsByteIdempotentWhenNothingChanged()
    {
        var catalog = BuildCatalog(Module("A"));
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(
                    DagLedgerLoader.Load(baselineBytes.AsSpan())).Syntax,
                catalog)).Capability;

        var candidateBytes = FrozenLedgerGenerator.AppendSynchronization(baseline, catalog);

        Assert.True(candidateBytes.AsSpan().SequenceEqual(baselineBytes.AsSpan()));
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

    private static byte[] WithoutRecordedAxiomClosures(ImmutableArray<byte> bytes)
    {
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(bytes.AsSpan())).Syntax;
        var result = ImmutableArray.CreateBuilder<byte>();
        var previous = FrozenLedgerCanonicalWriter.ZeroHash;
        for (var sequence = 0; sequence < syntax.Lines.Length; sequence++)
        {
            var line = syntax.Lines[sequence].Value;
            var payload = JsonNode.Parse(line.GetProperty("payload").GetRawText())!.AsObject();
            payload.Remove("axiom_closure");
            var encoded = FrozenLedgerCanonicalWriter.WriteEvent(
                line.GetProperty("event_type").GetString()!,
                JsonSerializer.SerializeToElement(payload),
                previous,
                sequence);
            result.AddRange(encoded.Bytes);
            previous = encoded.Hash;
        }

        return result.ToArray();
    }
}
