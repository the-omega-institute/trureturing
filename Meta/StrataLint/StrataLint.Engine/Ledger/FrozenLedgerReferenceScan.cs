using System.Collections.Immutable;
using System.Text.Json;
using Dunet;

namespace StrataLint.Engine;

public sealed class FrozenLedgerReferenceSet
{
    private FrozenLedgerReferenceSet(
        ImmutableArray<FrozenLedgerInput> inputs,
        ImmutableArray<string> revocationReceiptBlobOids)
    {
        Inputs = inputs;
        RevocationReceiptBlobOids = revocationReceiptBlobOids;
    }

    public ImmutableArray<FrozenLedgerInput> Inputs { get; }

    public ImmutableArray<string> RevocationReceiptBlobOids { get; }

    internal static FrozenLedgerReferenceSet Create(
        ImmutableArray<FrozenLedgerInput> inputs,
        ImmutableArray<string> receiptOids) =>
        new(inputs, receiptOids);
}

[Union(EnableImplicitConversions = false)]
public partial record FrozenLedgerReferenceScanOutcome
{
    public partial record Accepted(FrozenLedgerReferenceSet References);

    public partial record Rejected(string Message);
}

public static partial class FrozenLedger
{
    public static FrozenLedgerReferenceScanOutcome ScanReferences(FrozenLedgerSyntax syntax)
    {
        ArgumentNullException.ThrowIfNull(syntax);
        try
        {
            ValidateSyntaxEnvelope(syntax);
            if (syntax.Lines.Length == 0)
            {
                throw new FormatException("Frozen ledger is empty.");
            }

            var inputs = ImmutableArray.CreateBuilder<FrozenLedgerInput>();
            var receipts = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
            var previous = ZeroHash;
            for (var index = 0; index < syntax.Lines.Length; index++)
            {
                var line = syntax.Lines[index];
                var root = line.Value;
                RequireObjectFields(
                    root,
                    "event envelope",
                    "event_hash", "event_type", "payload", "previous_hash", "schema_version", "sequence");
                RequireCanonicalLine(line);
                var sequence = RequiredNonnegativeInteger(root, "sequence");
                var previousHash = RequiredString(root, "previous_hash");
                var eventHash = RequiredString(root, "event_hash");
                if (sequence != index
                    || RequiredNonnegativeInteger(root, "schema_version") != 1
                    || previousHash != previous
                    || !FrozenHashSyntax.IsSha256(eventHash)
                    || eventHash != ComputeEventHash(root))
                {
                    throw new FormatException("Frozen event sequence/hash chain is invalid.");
                }

                var eventType = RequiredString(root, "event_type");
                if (!root.TryGetProperty("payload", out var payload)
                    || payload.ValueKind != JsonValueKind.Object)
                {
                    throw new FormatException("Frozen event payload must be an object.");
                }

                if (index == 0 && eventType != "Genesis")
                {
                    throw new FormatException("Sequence zero must be Genesis.");
                }

                if (eventType == "Genesis")
                {
                    if (index != 0)
                    {
                        throw new FormatException("Genesis may occur only at sequence zero.");
                    }
                }
                else if (eventType is "Freeze" or "Reattest")
                {
                    if (!payload.TryGetProperty("input", out var input))
                    {
                        throw new FormatException($"{eventType} payload is missing input fields.");
                    }

                    inputs.Add(ParseInput(input));
                }
                else if (eventType == "Revoke")
                {
                    if (!payload.TryGetProperty("evidence", out var evidence)
                        || evidence.ValueKind != JsonValueKind.Array)
                    {
                        throw new FormatException("Revoke payload is missing evidence fields.");
                    }

                    foreach (var item in evidence.EnumerateArray().Select(ParseEvidence))
                    {
                        var (oid, _) = EvidenceReceipt(item);
                        if (!FrozenHashSyntax.IsGitOid(oid))
                        {
                            throw new FormatException("Revoke evidence receipt has a malformed Git blob OID.");
                        }

                        receipts.Add(oid);
                    }
                }
                else
                {
                    throw new FormatException($"Unknown frozen event type {eventType}.");
                }

                previous = eventHash;
            }

            return new FrozenLedgerReferenceScanOutcome.Accepted(FrozenLedgerReferenceSet.Create(
                inputs.ToImmutable(),
                receipts.Order(StringComparer.Ordinal).ToImmutableArray()));
        }
        catch (Exception exception) when (
            exception is FormatException or JsonException or InvalidOperationException or KeyNotFoundException)
        {
            return new FrozenLedgerReferenceScanOutcome.Rejected(exception.Message);
        }
    }
}
