using System.Collections.Immutable;
using System.Reflection;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed partial class RevocationTests
{
    [Fact]
    public void EvidenceUnionHasExactlyFourVariantsAndValidatedCapabilitiesArePrivate()
    {
        var variants = typeof(RevocationEvidence)
            .GetNestedTypes(BindingFlags.Public)
            .Where(type => type.BaseType == typeof(RevocationEvidence))
            .Select(static type => type.Name)
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(
            new[]
            {
                "AllowedAxiomRetired",
                "ContentAddressMismatch",
                "FormalContradictionCertificate",
                "KernelWitnessFailure",
            },
            variants);
        Assert.Empty(typeof(ValidatedRevocationEvidence).GetConstructors(BindingFlags.Instance | BindingFlags.Public));
        Assert.Empty(typeof(RevocationPlan).GetConstructors(BindingFlags.Instance | BindingFlags.Public));
        Assert.Empty(typeof(TrustedRevocationReceiptStore).GetConstructors(BindingFlags.Instance | BindingFlags.Public));
    }

    [Fact]
    public void EveryEvidenceVariantBindsAnActiveRootAndTrustedReceiptBytes()
    {
        var catalog = BuildCatalog(Module("A", axioms: new[] { "Classical.choice" }));
        var ledger = Genesis(catalog);
        var node = Assert.Single(ledger.ActiveFrozenNodes);
        RevocationEvidence[] provisional =
        {
            new RevocationEvidence.KernelWitnessFailure(
                node.FrozenNodeId,
                node.WitnessId,
                string.Empty,
                string.Empty),
            new RevocationEvidence.AllowedAxiomRetired(
                node.FrozenNodeId,
                "Classical.choice",
                string.Empty,
                string.Empty),
            new RevocationEvidence.FormalContradictionCertificate(
                node.FrozenNodeId,
                node.StatementId,
                string.Empty,
                string.Empty),
            new RevocationEvidence.ContentAddressMismatch(
                node.FrozenNodeId,
                node.FrozenNodeId.Value,
                Sha256("actual"),
                string.Empty,
                string.Empty),
        };
        var receipts = ReceiptStore(ledger, provisional);

        Assert.All(receipts.Evidence, item => Assert.IsType<RevocationEvidenceValidationOutcome.Accepted>(
            RevocationEvidenceValidator.Validate(item, ledger, receipts.Store)));
    }

    [Fact]
    public void TypedReceiptCannotBeReplayedAcrossEvidenceVariants()
    {
        var catalog = BuildCatalog(Module("A", axioms: new[] { "Classical.choice" }));
        var ledger = Genesis(catalog);
        var node = Assert.Single(ledger.ActiveFrozenNodes);
        var provisional = new RevocationEvidence.KernelWitnessFailure(
            node.FrozenNodeId,
            node.WitnessId,
            string.Empty,
            string.Empty);
        var receiptBytes = RevocationReceiptWriter.Write(ledger, provisional);
        var receiptText = Encoding.UTF8.GetString(receiptBytes.AsSpan());
        var receiptOid = GitBlobOid(receiptText);
        var receiptSha = Sha256(receiptText);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(new[]
            {
                new RawRepositoryEntry("Evidence/D5/revocation-receipt.json", receiptBytes),
            }))).Snapshot;
        var store = Assert.IsType<RevocationReceiptStoreOutcome.Accepted>(
            TrustedRevocationReceiptStore.Materialize(
                ledger,
                snapshot,
                new[] { receiptOid })).Capability;
        var valid = provisional with
        {
            ReceiptBlobOid = receiptOid,
            ReceiptSha256 = receiptSha,
        };
        var replay = new RevocationEvidence.AllowedAxiomRetired(
            node.FrozenNodeId,
            "Classical.choice",
            receiptOid,
            receiptSha);

        Assert.IsType<RevocationEvidenceValidationOutcome.Accepted>(
            RevocationEvidenceValidator.Validate(valid, ledger, store));
        var rejected = Assert.IsType<RevocationEvidenceValidationOutcome.Rejected>(
            RevocationEvidenceValidator.Validate(replay, ledger, store));
        Assert.Contains("typed", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void TypedReceiptCannotBeReplayedAcrossFrozenRoots()
    {
        var ledger = Genesis(BuildCatalog(Module("A"), Module("B")));
        var a = Node(ledger, "A");
        var b = Node(ledger, "B");
        var receipts = ReceiptStore(ledger, KernelFailure(a));
        var original = Assert.IsType<RevocationEvidence.KernelWitnessFailure>(receipts.Evidence[0]);
        var replay = original with
        {
            RootFrozenNodeId = b.FrozenNodeId,
            FailedWitnessId = b.WitnessId,
        };

        var rejected = Assert.IsType<RevocationEvidenceValidationOutcome.Rejected>(
            RevocationEvidenceValidator.Validate(replay, ledger, receipts.Store));

        Assert.Contains("typed", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void TypedReceiptCannotBeReplayedAfterTheProtectedLedgerHeadChanges()
    {
        var catalog = BuildCatalog(Module("A"));
        var ledger = Genesis(catalog);
        var node = Assert.Single(ledger.ActiveFrozenNodes);
        var receipts = ReceiptStore(ledger, KernelFailure(node));
        var freeze = Assert.IsType<FrozenLedgerEvent.Freeze>(ledger.Events[1]);
        var advancedBytes = FrozenLedgerGenerator.AppendReattestation(
            ledger,
            freeze.Payload.CaseId,
            freeze.Payload.Input);
        var advanced = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateCandidate(Load(advancedBytes), ledger, catalog)).Capability;

        var rejected = Assert.IsType<RevocationEvidenceValidationOutcome.Rejected>(
            RevocationEvidenceValidator.Validate(receipts.Evidence[0], advanced, receipts.Store));

        Assert.Contains("baseline", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void AllowedAxiomRetiredMustNameAnAxiomInTheActiveWitnessClosure()
    {
        var catalog = BuildCatalog(Module("A"));
        var ledger = Genesis(catalog);
        var node = Assert.Single(ledger.ActiveFrozenNodes);
        var evidence = new RevocationEvidence.AllowedAxiomRetired(
            node.FrozenNodeId,
            "Classical.choice",
            string.Empty,
            string.Empty);

        var rejected = Assert.Throws<FormatException>(() => RevocationReceiptWriter.Write(ledger, evidence));

        Assert.Contains("axiom closure", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ContentAddressMismatchExpectedAddressMustBeTheActiveFrozenNodeId()
    {
        var catalog = BuildCatalog(Module("A"));
        var ledger = Genesis(catalog);
        var node = Assert.Single(ledger.ActiveFrozenNodes);
        var evidence = new RevocationEvidence.ContentAddressMismatch(
            node.FrozenNodeId,
            Sha256("unrelated-expected-address"),
            Sha256("actual-address"),
            string.Empty,
            string.Empty);

        var rejected = Assert.Throws<FormatException>(() => RevocationReceiptWriter.Write(ledger, evidence));

        Assert.Contains("frozen", rejected.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void RevocationClosureUsesFrozenReverseEdgesAndDeduplicatesDiamondAndRoots()
    {
        var catalog = BuildCatalog(
            Module("A"),
            Module("B", imports: new[] { "A" }),
            Module("C", imports: new[] { "A" }),
            Module("D", imports: new[] { "B", "C" }));
        var ledger = Genesis(catalog);
        var b = Node(ledger, "B");
        var c = Node(ledger, "C");
        var receipts = ReceiptStore(
            ledger,
            KernelFailure(b),
            KernelFailure(c));
        var bEvidence = ValidateEvidence(receipts.Evidence[0], ledger, receipts.Store);
        var cEvidence = ValidateEvidence(receipts.Evidence[1], ledger, receipts.Store);

        var bPlan = Assert.IsType<RevocationPlanOutcome.Accepted>(
            RevocationPlanner.Plan(ledger, new[] { bEvidence, bEvidence })).Capability;
        var multiPlan = Assert.IsType<RevocationPlanOutcome.Accepted>(
            RevocationPlanner.Plan(ledger, new[] { bEvidence, cEvidence })).Capability;

        Assert.Equal(new[] { "B", "D" }, Names(ledger, bPlan.AffectedFrozenNodeIds));
        Assert.Single(bPlan.RootFrozenNodeIds);
        Assert.Equal(new[] { "B", "C", "D" }, Names(ledger, multiPlan.AffectedFrozenNodeIds));
        Assert.Equal(3, multiPlan.AffectedFrozenNodeIds.Distinct().Count());
        Assert.Matches("^sha256:[0-9a-f]{64}$", multiPlan.ClosureHash);
    }

    [Fact]
    public void TombstonePreventsReactivationAndCorrectionRequiresANewFrozenNodeId()
    {
        var baselineCatalog = BuildCatalog(Module("A"));
        var baseline = Genesis(baselineCatalog);
        var oldNode = Assert.Single(baseline.ActiveFrozenNodes);
        var receipts = ReceiptStore(baseline, KernelFailure(oldNode));
        var evidence = ValidateEvidence(receipts.Evidence[0], baseline, receipts.Store);
        var plan = Assert.IsType<RevocationPlanOutcome.Accepted>(
            RevocationPlanner.Plan(baseline, new[] { evidence })).Capability;
        var revokeBytes = FrozenLedgerGenerator.AppendRevocation(baseline, plan);
        var emptyCatalog = BuildCatalog();
        var revoked = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateCandidate(Load(revokeBytes), baseline, emptyCatalog, receipts.Store)).Capability;

        Assert.Empty(revoked.ActiveFrozenNodes);
        Assert.Contains(oldNode.FrozenNodeId, revoked.RevokedFrozenNodeIds);

        var deletedTombstone = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(
                Load(baseline.RawBytes),
                revoked,
                emptyCatalog,
                receipts.Store));
        Assert.Contains("prefix", deletedTombstone.Message, StringComparison.OrdinalIgnoreCase);

        var resurrectBytes = FrozenLedgerGenerator.AppendMissingFreezes(revoked, baselineCatalog);
        var resurrected = Assert.IsType<FrozenLedgerValidationOutcome.Rejected>(
            ValidateCandidate(Load(resurrectBytes), baseline, baselineCatalog, receipts.Store));
        Assert.Contains("missing Freeze", resurrected.Message, StringComparison.OrdinalIgnoreCase);

        var correctedCatalog = BuildCatalog(Module(
            "A",
            source: "theorem a : True := by exact True.intro\n"));
        var correctedNode = Assert.Single(correctedCatalog.ClosedNodes);
        Assert.NotEqual(oldNode.FrozenNodeId, correctedNode.FrozenNodeId);
        var correctedBytes = FrozenLedgerGenerator.AppendMissingFreezes(revoked, correctedCatalog);
        var corrected = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateCandidate(Load(correctedBytes), baseline, correctedCatalog, receipts.Store)).Capability;
        Assert.Equal(correctedNode.FrozenNodeId, Assert.Single(corrected.ActiveFrozenNodes).FrozenNodeId);
    }

    [Fact]
    public void ProtectedHistoryWithARevocationCanBeReloadedAsTheNextBaseline()
    {
        var originalCatalog = BuildCatalog(
            Module("A"),
            Module("B", imports: new[] { "A" }));
        var genesis = Genesis(originalCatalog);
        var root = Node(genesis, "A");
        var receipts = ReceiptStore(genesis, KernelFailure(root));
        var evidence = ValidateEvidence(receipts.Evidence[0], genesis, receipts.Store);
        var plan = Assert.IsType<RevocationPlanOutcome.Accepted>(
            RevocationPlanner.Plan(genesis, new[] { evidence })).Capability;
        var historyBytes = FrozenLedgerGenerator.AppendRevocation(genesis, plan);
        var emptyCatalog = BuildCatalog();
        var admittedSuffix = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateCandidate(Load(historyBytes), genesis, emptyCatalog, receipts.Store)).Capability;

        var reloaded = Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateHistory(Load(historyBytes), emptyCatalog));

        Assert.Equal(admittedSuffix.HeadHash, reloaded.Capability.HeadHash);
        Assert.Empty(reloaded.Capability.ActiveFrozenNodes);
        Assert.Equal(2, reloaded.Capability.RevokedFrozenNodeIds.Count);
    }

    private static FrozenLedgerConsistent Genesis(FrozenMaterialCatalog catalog)
    {
        var bytes = FrozenLedgerGenerator.GenerateGenesis(
            catalog,
            new FrozenGenesisDescriptor(GitOid('e'), RuleCatalog.Default.RootSha256));
        return Assert.IsType<FrozenLedgerValidationOutcome.Accepted>(
            ValidateGenesis(Load(bytes), catalog)).Capability;
    }

    private static FrozenLedgerSyntax Load(IEnumerable<byte> bytes)
    {
        var array = bytes.ToArray();
        return Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(array)).Syntax;
    }

    private static (ImmutableArray<RevocationEvidence> Evidence, TrustedRevocationReceiptStore Store) ReceiptStore(
        FrozenLedgerConsistent ledger,
        params RevocationEvidence[] provisional)
    {
        var evidence = ImmutableArray.CreateBuilder<RevocationEvidence>();
        var entries = ImmutableArray.CreateBuilder<RawRepositoryEntry>();
        var oids = ImmutableArray.CreateBuilder<string>();
        foreach (var (item, index) in provisional.Select((item, index) => (item, index)))
        {
            var bytes = RevocationReceiptWriter.Write(ledger, item);
            var text = Encoding.UTF8.GetString(bytes.AsSpan());
            var oid = GitBlobOid(text);
            var sha = Sha256(text);
            evidence.Add(WithReceipt(item, oid, sha));
            entries.Add(new RawRepositoryEntry($"Evidence/D5/revocation-{index}.json", bytes));
            oids.Add(oid);
        }

        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries))).Snapshot;
        var store = Assert.IsType<RevocationReceiptStoreOutcome.Accepted>(
            TrustedRevocationReceiptStore.Materialize(ledger, snapshot, oids)).Capability;
        return (evidence.ToImmutable(), store);
    }

    private static RevocationEvidence KernelFailure(FrozenNodeMaterial node) =>
        new RevocationEvidence.KernelWitnessFailure(
            node.FrozenNodeId,
            node.WitnessId,
            string.Empty,
            string.Empty);

    private static ValidatedRevocationEvidence ValidateEvidence(
        RevocationEvidence evidence,
        FrozenLedgerConsistent ledger,
        TrustedRevocationReceiptStore receipts)
    {
        return Assert.IsType<RevocationEvidenceValidationOutcome.Accepted>(
            RevocationEvidenceValidator.Validate(evidence, ledger, receipts)).Capability;
    }

    private static RevocationEvidence WithReceipt(
        RevocationEvidence evidence,
        string oid,
        string sha) => evidence switch
        {
            RevocationEvidence.KernelWitnessFailure item => item with
            {
                ReceiptBlobOid = oid,
                ReceiptSha256 = sha,
            },
            RevocationEvidence.AllowedAxiomRetired item => item with
            {
                ReceiptBlobOid = oid,
                ReceiptSha256 = sha,
            },
            RevocationEvidence.FormalContradictionCertificate item => item with
            {
                ReceiptBlobOid = oid,
                ReceiptSha256 = sha,
            },
            RevocationEvidence.ContentAddressMismatch item => item with
            {
                ReceiptBlobOid = oid,
                ReceiptSha256 = sha,
            },
            _ => throw new InvalidOperationException("unknown evidence variant"),
        };

    private static FrozenNodeMaterial Node(FrozenLedgerConsistent ledger, string module) =>
        ledger.ActiveFrozenNodes.Single(node => node.RepoPath.Value == PathFor(module));

    private static string[] Names(
        FrozenLedgerConsistent ledger,
        IEnumerable<FrozenNodeId> ids) =>
        ids.Select(id => ledger.ActiveFrozenNodes.Single(node => node.FrozenNodeId == id))
            .Select(static node => Path.GetFileNameWithoutExtension(node.RepoPath.Value))
            .Order(StringComparer.Ordinal)
            .ToArray();
}
