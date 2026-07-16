using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ContractEpochStoreTests
{
    private const string LedgerPath = "Meta/contract-epoch/events.jsonl";
    private const string RetiredPath = "Meta/StrataLint/Golden/values-kernels.toml";
    private static readonly string TreeOid = "git-sha1:" + new string('a', 40);

    [Fact]
    public void SnapshotWithoutContractEpochDataLoadsAnEmptyStore()
    {
        var store = ContractEpochStore.Load(Snapshot(
            RawRepositoryEntry.FromText("README.md", "repository\n")));

        Assert.Empty(store.Ledger.Events);
        Assert.Empty(store.Receipts);
    }

    [Fact]
    public void StoreLoadsCanonicalLedgerAndContentAddressedEvidence()
    {
        var (ledger, receipt) = Registration();
        var evidencePath = EvidencePath(receipt.Reference);
        var store = ContractEpochStore.Load(Snapshot(
            new RawRepositoryEntry(LedgerPath, ledger),
            new RawRepositoryEntry(evidencePath, receipt.CanonicalBytes),
            RawRepositoryEntry.FromText("Meta/ReplacementLoader.cs", "sealed class Loader {}\n")));

        Assert.Single(store.Ledger.Events);
        var loadedReceipt = Assert.Single(store.Receipts).Value;
        Assert.Equal(receipt.Reference, loadedReceipt.Reference);
        Assert.Equal(receipt.CanonicalBytes.ToArray(), loadedReceipt.CanonicalBytes.ToArray());
        Assert.Contains("Meta/ReplacementLoader.cs", store.ExistingPaths);
    }

    [Fact]
    public void EvidenceFilenameMustEqualItsCanonicalContentRoot()
    {
        var (ledger, receipt) = Registration();
        var wrongPath = "Meta/contract-epoch/evidence/sha256/" + new string('b', 64) + ".json";

        var exception = Assert.Throws<FormatException>(() => ContractEpochStore.Load(Snapshot(
            new RawRepositoryEntry(LedgerPath, ledger),
            new RawRepositoryEntry(wrongPath, receipt.CanonicalBytes))));

        Assert.Contains("content root", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void EvidenceSetMustExactlyEqualRegisteredReferences()
    {
        var (_, receipt) = Registration();

        var exception = Assert.Throws<FormatException>(() => ContractEpochStore.Load(Snapshot(
            new RawRepositoryEntry(LedgerPath, ImmutableArray<byte>.Empty),
            new RawRepositoryEntry(EvidencePath(receipt.Reference), receipt.CanonicalBytes))));

        Assert.Contains("evidence set", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void ContractEpochNamespaceIsClosedToUnknownFiles()
    {
        var exception = Assert.Throws<FormatException>(() => ContractEpochStore.Load(Snapshot(
            new RawRepositoryEntry(LedgerPath, ImmutableArray<byte>.Empty),
            RawRepositoryEntry.FromText("Meta/contract-epoch/free-pass.json", "{}\n"))));

        Assert.Contains("unknown", exception.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void StoreExportsC0AnchorsOnlyFromACanonicalPhasedGate()
    {
        var records = C0Records();
        var store = ContractEpochStore.Load(Snapshot(
            RawRepositoryEntry.FromText(RepositoryRules.TowerManifestPath, Tower(records))));

        Assert.Equal(records, store.C0Anchors.Order(StringComparer.Ordinal).ToArray());
        Assert.DoesNotContain("phase1-protected-content-admission", store.C0Anchors);
    }

    [Fact]
    public void IncompleteC0CeremonyCannotCreateMachineCustodians()
    {
        var records = C0Records()
            .Where(static item => !item.StartsWith("c0/gate-wiring", StringComparison.Ordinal))
            .ToArray();

        var exception = Assert.Throws<FormatException>(() => ContractEpochStore.Load(Snapshot(
            RawRepositoryEntry.FromText(RepositoryRules.TowerManifestPath, Tower(records)))));

        Assert.Contains("C0", exception.Message, StringComparison.Ordinal);
    }

    private static (ImmutableArray<byte> Ledger, ContractEpochEvidenceReceipt Receipt) Registration()
    {
        var baseline = ConservativePolicySnapshot.Current();
        var candidate = baseline.WithExactExclusions([RetiredPath]);
        var receipt = ContractEpochEvidenceReceipt.UnreachabilityForPaths(
            candidate.Root,
            [RetiredPath]);
        var registration = new ContractEpochEvent.Register(
            "CONTRACT-STORE-001",
            TreeOid,
            baseline.Root,
            candidate.Root,
            new TransitionPlan.AuthorityDischargeV1(
                [RetiredPath],
                null,
                receipt.Reference));
        return (ContractEpochLedgerCodec.Write([registration]), receipt);
    }

    private static string EvidencePath(string reference) =>
        "Meta/contract-epoch/evidence/sha256/" + reference["sha256:".Length..] + ".json";

    private static string[] C0Records() =>
    [
        "c0/base-commit git-commit/" + new string('a', 40),
        "c0/ceremony-commit convention/this-pr-merge-commit",
        "c0/controller git-sha1/" + new string('b', 40) + " Meta/ReplacementLoader.cs",
        "c0/corpus git-sha1/" + new string('c', 40) + " Meta/Corpus.toml",
        "c0/gate-wiring git-sha1/" + new string('d', 40) + " .github/scripts/harness-gate.sh",
        "c0/inaugural-certificate sha256/" + new string('e', 64) + " Meta/Certificate.json",
        "c0/preimage-commit git-commit/" + new string('f', 40),
        "c0/preimage-tree git-tree/" + new string('a', 40),
    ];

    private static string Tower(IEnumerable<string> records) => string.Join("\n",
        new[]
        {
            "schema_version: 1",
            "components:",
            "  - id: conservative-extension-gate-c",
            "    kind: phased-gate",
            "    members:",
            "      - phase1-protected-content-admission",
            "      - phase2-dual-harness-conservative-extension",
        }
        .Concat(records.Select(static item => "      - \"" + item + "\""))
        .Concat(
        [
            "    judged_by:",
            "      - bootstrap-pr-1",
            "    verification: verified",
            "bootstrap:",
            "  id: bootstrap-pr-1",
            "  judge: open",
            "  reason: \"Godel boundary: the trust root cannot prove its own consistency.\"",
            "  genesis_event: sha256:" + new string('a', 64),
            "  commit: " + new string('b', 40),
            "  pull_request: 1",
            "  verification: ASSUMED-UNVERIFIED",
            string.Empty,
        ]));

    private static RepositorySnapshot Snapshot(params RawRepositoryEntry[] entries) =>
        SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries)) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
}
