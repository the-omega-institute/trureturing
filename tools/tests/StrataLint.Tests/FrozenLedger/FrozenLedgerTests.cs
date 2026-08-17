using System.Collections.Immutable;
using System.Reflection;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class FrozenLedgerTests
{
    [Fact]
    public void ReferenceProjectionRejectsUnknownFieldsForEveryEventPayloadSchema()
    {
        var catalog = BuildCatalog(Module("A"));
        var genesis = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var genesisSyntax = Loaded(genesis.AsSpan());
        var history = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(genesisSyntax, catalog)).Capability;
        var reattest = FrozenLedgerGenerator.AppendReattestation(
            history,
            Assert.Single(history.ActiveEntries).Key,
            Assert.Single(Assert.IsType<FrozenLedgerReferenceScanOutcome.Accepted>(
                FrozenLedger.ScanReferences(genesisSyntax)).References.Inputs));
        var revokePayload = JsonSerializer.SerializeToElement(new
        {
            affected_case_ids = Array.Empty<string>(),
            affected_frozen_node_ids = Array.Empty<string>(),
            closure_hash = FrozenLedgerCanonicalWriter.ZeroHash,
            evidence = Array.Empty<object>(),
            graph_root = FrozenLedgerCanonicalWriter.ZeroHash,
            root_case_ids = Array.Empty<string>(),
        });
        var revokeLine = FrozenLedgerCanonicalWriter.WriteEvent(
            "Revoke",
            revokePayload,
            genesisSyntax.Lines[0].Value.GetProperty("event_hash").GetString()!,
            1).Bytes;

        AssertUnknownPayloadFieldRejected(genesisSyntax.RawBytes, 0);
        AssertUnknownPayloadFieldRejected(genesisSyntax.RawBytes, 1);
        AssertUnknownPayloadFieldRejected(reattest, 2);
        var supersedeFixture = SupersedeFixture();
        AssertUnknownPayloadFieldRejected(
            AppendSupersede(supersedeFixture),
            supersedeFixture.Baseline.Events.Length);
        AssertUnknownPayloadFieldRejected(genesisSyntax.Lines[0].RawBytes.AddRange(revokeLine), 1);
    }

    [Fact]
    public void LedgerCapabilityAndContentAddressIdentifiersHaveNoPublicConstructors()
    {
        Assert.Empty(typeof(FrozenLedgerConsistent).GetConstructors(BindingFlags.Instance | BindingFlags.Public));
        Assert.Empty(typeof(FrozenMaterialCatalog).GetConstructors(BindingFlags.Instance | BindingFlags.Public));
        Assert.Empty(typeof(StatementId).GetConstructors(BindingFlags.Instance | BindingFlags.Public));
        Assert.Empty(typeof(WitnessId).GetConstructors(BindingFlags.Instance | BindingFlags.Public));
        Assert.Empty(typeof(FrozenNodeId).GetConstructors(BindingFlags.Instance | BindingFlags.Public));
        Assert.Empty(typeof(TrustedFrozenGitReferences).GetConstructors(BindingFlags.Instance | BindingFlags.Public));
    }

    [Fact]
    public void GenesisFreezesEveryClosedModuleAndValidatesToAPrivateCapability()
    {
        var catalog = BuildCatalog(
            Module("A"),
            Module("B", imports: new[] { "A" }));
        var bytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(
                GitOid('e'),
                RuleCatalog.Default.RootSha256));
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes.AsSpan())).Syntax;

        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(syntax, catalog));

        Assert.Equal(3, accepted.Capability.Events.Length);
        Assert.Equal(2, accepted.Capability.ActiveFrozenNodes.Length);
        Assert.Equal(
            catalog.ClosedNodes.Select(static node => node.FrozenNodeId),
            accepted.Capability.ActiveFrozenNodes.Select(static node => node.FrozenNodeId));
        Assert.Matches("^sha256:[0-9a-f]{64}$", accepted.Capability.HeadHash);
        Assert.Matches("^sha256:[0-9a-f]{64}$", accepted.Capability.CorpusRoot);
    }

    [Fact]
    public void SemanticallyEqualButNoncanonicalEventBytesFailClosed()
    {
        var catalog = BuildCatalog(Module("A"));
        var canonical = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var text = Encoding.UTF8.GetString(canonical.AsSpan());
        var noncanonical = Encoding.UTF8.GetBytes(text.Replace(": ", ":", StringComparison.Ordinal));
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(noncanonical)).Syntax;

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateGenesis(syntax, catalog));

        Assert.Contains("canonical", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ACanonicalTruncationThatDropsAFreezeFailsAsMissingClosedMaterial()
    {
        var catalog = BuildCatalog(Module("A"), Module("B"));
        var complete = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var lines = Lines(complete);
        var truncated = lines.Take(lines.Length - 1).SelectMany(static line => line).ToArray();
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(truncated)).Syntax;

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateGenesis(syntax, catalog));

        Assert.Contains("missing Freeze", rejected.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ForgedPreviousHashFailsEvenWhenTheLineRemainsCanonicalJson()
    {
        var catalog = BuildCatalog(Module("A"));
        var complete = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var lines = Lines(complete);
        var second = Encoding.UTF8.GetString(lines[1]);
        var previous = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(lines[0])).Syntax;
        var genesis = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateGenesis(previous, catalog));
        Assert.Contains("missing Freeze", genesis.Message, StringComparison.Ordinal);
        var priorHash = Encoding.UTF8.GetString(lines[0]);
        var hashStart = priorHash.IndexOf("\"event_hash\": \"", StringComparison.Ordinal) + 15;
        var priorEventHash = priorHash.Substring(hashStart, 71);
        var forgedHash = priorEventHash[..^1] + (priorEventHash[^1] == '0' ? '1' : '0');
        var forgedSecond = Encoding.UTF8.GetBytes(second.Replace(priorEventHash, forgedHash, StringComparison.Ordinal));
        var forged = lines[0].Concat(forgedSecond).ToArray();
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(forged)).Syntax;

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateGenesis(syntax, catalog));

        Assert.Contains("chain", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void CandidateLedgerMustRetainTheExactValidatedBaselineBytesAsPrefix()
    {
        var catalog = BuildCatalog(Module("A"));
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baselineSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(baselineBytes.AsSpan())).Syntax;
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(baselineSyntax, catalog)).Capability;
        var rewrittenBytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('f'), RuleCatalog.Default.RootSha256));
        var rewritten = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(rewrittenBytes.AsSpan())).Syntax;

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(rewritten, baseline, catalog));

        Assert.Contains("prefix", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void OpenModuleWithoutAPermanentCaseIdCannotEnterFrozenLedgerMaterial()
    {
        const string path = "D5/X_Frontier/UnregisteredOpen.lean";
        var outcome = BuildCatalogOutcome(
            path,
            "theorem unresolved : True := by sorry\n",
            new LeanFileReport(
                ImmutableArray<string>.Empty,
                ImmutableArray.Create(new LeanDeclaration(
                    "unresolved",
                    "theorem",
                    "True",
                    ImmutableArray.Create("sorryAx")))));

        var rejected = Assert.IsType<FrozenMaterialOutcome.Rejected>(outcome);
        Assert.Contains("CaseId", rejected.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void TailModuleWithoutAnAssumptionRegistrationReferenceFailsClosed()
    {
        const string path = "D5/S0/Carrier/UnregisteredDebt.lean";
        var outcome = BuildCatalogOutcome(
            path,
            "axiom debt : False\n",
            new LeanFileReport(
                ImmutableArray<string>.Empty,
                ImmutableArray.Create(new LeanDeclaration(
                    "debt",
                    "axiom",
                    "False",
                    ImmutableArray.Create("debt")))));

        var rejected = Assert.IsType<FrozenMaterialOutcome.Rejected>(outcome);
        Assert.Contains("registration", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void NewClosedModuleRequiresAnAppendedFreezeBeforeCandidateValidationCanPass()
    {
        var baselineCatalog = BuildCatalog(Module("A"));
        var candidateCatalog = BuildCatalog(Module("A"), Module("B", imports: new[] { "A" }));
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            baselineCatalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baselineSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(baselineBytes.AsSpan())).Syntax;
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(baselineSyntax, baselineCatalog)).Capability;

        var missing = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(baselineSyntax, baseline, candidateCatalog));
        Assert.Contains("missing Freeze", missing.Message, StringComparison.Ordinal);

        var candidateBytes = FrozenLedgerGenerator.AppendMissingFreezes(baseline, candidateCatalog);
        var candidateSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(candidateBytes.AsSpan())).Syntax;
        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateCandidate(candidateSyntax, baseline, candidateCatalog));

        Assert.Equal(2, accepted.Capability.ActiveFrozenNodes.Length);
        Assert.Equal(2, accepted.Capability.Events.OfType<FrozenLedgerEvent.Freeze>().Count());
    }

    [Fact]
    public void PostGenesisFreezeCarriesItsOwnCommitAndTreeAttestation()
    {
        var baselineCatalog = BuildCatalog(Module("A"));
        var candidateCatalog = BuildCatalog(
            Module("A"),
            Module(
                "B",
                imports: new[] { "A" },
                baseCommitOid: GitOid('f'),
                baseTreeOid: GitOid('1')));
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            baselineCatalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(
                    DagLedgerLoader.Load(baselineBytes.AsSpan())).Syntax,
                baselineCatalog)).Capability;

        var candidateBytes = FrozenLedgerGenerator.AppendMissingFreezes(baseline, candidateCatalog);
        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateCandidate(
                Assert.IsType<DagLedgerLoadOutcome.Loaded>(
                    DagLedgerLoader.Load(candidateBytes.AsSpan())).Syntax,
                baseline,
                candidateCatalog)).Capability;
        var appended = accepted.Events.OfType<FrozenLedgerEvent.Freeze>()
            .Single(static item => item.Payload.Input.DescriptorSelector.EndsWith("/B.lean", StringComparison.Ordinal));

        Assert.Equal(GitOid('f'), appended.Payload.Input.BaseCommitOid);
        Assert.Equal(GitOid('1'), appended.Payload.Input.BaseTreeOid);
    }

    [Fact]
    public void ReattestCanRefreshReachabilityWithoutChangingFrozenIdentity()
    {
        var catalog = BuildCatalog(Module("A"));
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baselineSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(baselineBytes.AsSpan())).Syntax;
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(baselineSyntax, catalog)).Capability;
        var freeze = Assert.IsType<FrozenLedgerEvent.Freeze>(baseline.Events[1]);
        var refreshedInput = freeze.Payload.Input with
        {
            BaseCommitOid = GitOid('f'),
            BaseTreeOid = GitOid('1'),
        };

        var candidateBytes = FrozenLedgerGenerator.AppendReattestation(
            baseline,
            freeze.Payload.CaseId,
            refreshedInput);
        var candidateSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(candidateBytes.AsSpan())).Syntax;
        var accepted = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateCandidate(candidateSyntax, baseline, catalog));

        Assert.Equal(
            baseline.ActiveFrozenNodes.Single().FrozenNodeId,
            accepted.Capability.ActiveFrozenNodes.Single().FrozenNodeId);
        Assert.NotEqual(baseline.HeadHash, accepted.Capability.HeadHash);
        var reattestPayload = candidateSyntax.Lines[^1].Value.GetProperty("payload");
        Assert.Equal(
            new[]
            {
                "axiom_closure",
                "case_id",
                "input",
                "previous_attestation_event_hash",
            },
            reattestPayload.EnumerateObject()
                .Select(static property => property.Name)
                .Order(StringComparer.Ordinal));
        Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(candidateSyntax, catalog));
    }

    [Fact]
    public void ReattestFailsWhenItsCommitAndTreeWereNotValidatedByTheGitAdapter()
    {
        var catalog = BuildCatalog(Module("A"));
        var baselineBytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        var baselineSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(baselineBytes.AsSpan())).Syntax;
        var baselineReferences = TrustedFrozenGitReferences.CreateForTrustedAdapter(
            Assert.IsType<FrozenLedgerReferenceScanOutcome.Accepted>(
                FrozenLedger.ScanReferences(baselineSyntax)).References.Inputs);
        var baseline = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(baselineSyntax, catalog, baselineReferences)).Capability;
        var freeze = Assert.IsType<FrozenLedgerEvent.Freeze>(baseline.Events[1]);
        var candidateBytes = FrozenLedgerGenerator.AppendReattestation(
            baseline,
            freeze.Payload.CaseId,
            freeze.Payload.Input with
            {
                BaseCommitOid = GitOid('f'),
                BaseTreeOid = GitOid('1'),
            });
        var candidateSyntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(
            DagLedgerLoader.Load(candidateBytes.AsSpan())).Syntax;

        var rejected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                candidateSyntax,
                baseline,
                catalog,
                baselineReferences,
                TrustedRevocationReceiptStore.Empty(baseline)));

        Assert.Contains("Git", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    private static FrozenLedgerSyntax Loaded(ReadOnlySpan<byte> bytes) =>
        Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes)).Syntax;

    private static void AssertUnknownPayloadFieldRejected(
        ImmutableArray<byte> ledger,
        int eventIndex)
    {
        var syntax = Loaded(ledger.AsSpan());
        var prefix = syntax.Lines.Take(eventIndex).SelectMany(static line => line.RawBytes).ToArray();
        var target = syntax.Lines[eventIndex].Value;
        var payload = target.GetProperty("payload").EnumerateObject()
            .ToDictionary(
                static property => property.Name,
                static property => property.Value.Clone(),
                StringComparer.Ordinal);
        payload.Add("unknown_oid", JsonSerializer.SerializeToElement(GitOid('f')));
        var rewritten = FrozenLedgerCanonicalWriter.WriteEvent(
            target.GetProperty("event_type").GetString()!,
            JsonSerializer.SerializeToElement(payload),
            target.GetProperty("previous_hash").GetString()!,
            eventIndex).Bytes;
        var rejected = Assert.IsType<FrozenLedgerReferenceScanOutcome.Rejected>(
            FrozenLedger.ScanReferences(Loaded(prefix.Concat(rewritten).ToArray())));

        Assert.Contains("unknown, missing, or duplicate fields", rejected.Message, StringComparison.Ordinal);
    }

}
