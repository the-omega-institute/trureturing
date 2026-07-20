using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed class ContractEpochStore
{
    private const string LedgerPath = "Meta/contract-epoch/events.jsonl";
    private const string NamespacePrefix = "Meta/contract-epoch/";
    private const string EvidencePrefix = "Meta/contract-epoch/evidence/sha256/";
    private const string EvidenceSuffix = ".json";

    private ContractEpochStore(
        ContractEpochLedger ledger,
        ImmutableDictionary<string, ContractEpochEvidenceReceipt> receipts,
        ImmutableHashSet<string> existingPaths,
        ImmutableHashSet<string> c0Anchors)
    {
        Ledger = ledger;
        Receipts = receipts;
        ExistingPaths = existingPaths;
        C0Anchors = c0Anchors;
    }

    internal static ContractEpochStore Empty { get; } = new(
        ContractEpochLedger.Empty,
        ImmutableDictionary<string, ContractEpochEvidenceReceipt>.Empty.WithComparers(
            StringComparer.Ordinal),
        ImmutableHashSet<string>.Empty.WithComparer(StringComparer.Ordinal),
        ImmutableHashSet<string>.Empty.WithComparer(StringComparer.Ordinal));

    internal ContractEpochLedger Ledger { get; }

    internal ImmutableDictionary<string, ContractEpochEvidenceReceipt> Receipts { get; }

    internal ImmutableHashSet<string> ExistingPaths { get; }

    internal ImmutableHashSet<string> C0Anchors { get; }

    internal static ContractEpochStore Load(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        var files = snapshot.Files.Values.ToDictionary(
            static file => file.Path.Value,
            StringComparer.Ordinal);
        foreach (var path in files.Keys.Where(static path =>
            path.StartsWith(NamespacePrefix, StringComparison.Ordinal)))
        {
            if (!string.Equals(path, LedgerPath, StringComparison.Ordinal)
                && !TryEvidenceReference(path, out _))
            {
                throw new FormatException($"contract epoch namespace contains an unknown file: {path}");
            }
        }

        var ledger = files.TryGetValue(LedgerPath, out var ledgerFile)
            ? ContractEpochLedgerCodec.Read(ledgerFile.RawBytes.AsSpan())
            : ContractEpochLedger.Empty;
        var receipts = ImmutableDictionary.CreateBuilder<string, ContractEpochEvidenceReceipt>(
            StringComparer.Ordinal);
        foreach (var (path, file) in files.OrderBy(static item => item.Key, StringComparer.Ordinal))
        {
            if (!TryEvidenceReference(path, out var expectedReference)) continue;
            var receipt = ContractEpochEvidenceReceipt.Read(file.RawBytes.AsSpan());
            if (!string.Equals(receipt.Reference, expectedReference, StringComparison.Ordinal))
            {
                throw new FormatException(
                    $"contract evidence filename does not equal its content root: {path}");
            }

            receipts.Add(receipt.Reference, receipt);
        }

        var referenced = ledger.Events
            .OfType<ContractEpochEvent.Register>()
            .Select(static item => item.Plan switch
            {
                TransitionPlan.CustodyTransferV1 transfer => transfer.Receipt,
                TransitionPlan.AuthorityDischargeV1 discharge => discharge.UnreachabilityProofRef,
                _ => throw new InvalidOperationException("unknown transition plan"),
            })
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        if (!referenced.SequenceEqual(receipts.Keys.Order(StringComparer.Ordinal), StringComparer.Ordinal))
        {
            throw new FormatException(
                "contract epoch evidence set must exactly equal registered references");
        }

        return new ContractEpochStore(
            ledger,
            receipts.ToImmutable(),
            files.Keys.ToImmutableHashSet(StringComparer.Ordinal),
            LoadC0Anchors(snapshot));
    }

    internal ContractEpochEvidenceIndex EvidenceWithCustodiansFrom(ContractEpochStore candidate)
    {
        ArgumentNullException.ThrowIfNull(candidate);
        return ContractEpochEvidenceIndex.Create(
            Receipts.Values,
            candidate.ExistingPaths,
            candidate.C0Anchors);
    }

    private static bool TryEvidenceReference(string path, out string reference)
    {
        reference = string.Empty;
        if (!path.StartsWith(EvidencePrefix, StringComparison.Ordinal)
            || !path.EndsWith(EvidenceSuffix, StringComparison.Ordinal))
        {
            return false;
        }

        var digest = path[EvidencePrefix.Length..^EvidenceSuffix.Length];
        if (digest.Length != 64
            || digest.Any(static character =>
                character is not (>= '0' and <= '9') and not (>= 'a' and <= 'f')))
        {
            return false;
        }

        reference = "sha256:" + digest;
        return true;
    }

    private static ImmutableHashSet<string> LoadC0Anchors(RepositorySnapshot snapshot)
    {
        return C0CeremonyProjection.TryCreateAnchorAddressRecords(snapshot, out var records)
            ? records.ToImmutableHashSet(StringComparer.Ordinal)
            : ImmutableHashSet<string>.Empty.WithComparer(StringComparer.Ordinal);
    }

}
