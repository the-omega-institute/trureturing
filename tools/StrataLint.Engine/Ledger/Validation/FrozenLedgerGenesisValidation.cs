using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

public static partial class FrozenLedger
{
    private const string ZeroHash = "sha256:0000000000000000000000000000000000000000000000000000000000000000";

    public static FrozenLedgerValidationOutcome ValidateGenesis(
        FrozenLedgerSyntax syntax,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences trustedReferences)
    {
        ArgumentNullException.ThrowIfNull(syntax);
        ArgumentNullException.ThrowIfNull(catalog);
        ArgumentNullException.ThrowIfNull(trustedReferences);
        try
        {
            ValidateSyntaxEnvelope(syntax);
            if (syntax.Lines.Length == 0)
            {
                throw new FormatException("Frozen ledger is empty.");
            }

            var events = ImmutableArray.CreateBuilder<FrozenLedgerEvent>(syntax.Lines.Length);
            var freezes = new Dictionary<RepoPath, (
                FrozenNodeMaterial Material,
                FrozenFreezePayload Payload,
                string LastAttestationEventHash)>();
            var freezeOrder = ImmutableArray.CreateBuilder<(string CaseClass, string CaseId)>();
            var caseIds = new HashSet<string>(StringComparer.Ordinal);
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
                if (sequence != index || RequiredNonnegativeInteger(root, "schema_version") != 1)
                {
                    throw new FormatException("Frozen event sequence/schema is not continuous v1.");
                }

                var previousHash = RequiredString(root, "previous_hash");
                var eventHash = RequiredString(root, "event_hash");
                if (!string.Equals(previousHash, previous, StringComparison.Ordinal)
                    || !FrozenHashSyntax.IsSha256(eventHash)
                    || !string.Equals(eventHash, ComputeEventHash(root), StringComparison.Ordinal))
                {
                    throw new FormatException("Frozen event previous-hash/event-hash chain is invalid.");
                }

                var eventType = RequiredString(root, "event_type");
                var payload = root.GetProperty("payload");
                if (index == 0)
                {
                    if (!string.Equals(eventType, "Genesis", StringComparison.Ordinal))
                    {
                        throw new FormatException("Sequence zero must be Genesis.");
                    }

                    events.Add(new FrozenLedgerEvent.Genesis(
                        sequence,
                        eventHash,
                        previousHash,
                        ParseGenesis(payload, catalog)));
                }
                else if (string.Equals(eventType, "Freeze", StringComparison.Ordinal))
                {
                    var freeze = ParseFreeze(payload, catalog, trustedReferences);
                    var freezePath = RepoPath.CreateKnown(freeze.Input.DescriptorSelector);
                    if (!freezes.TryAdd(
                            freezePath,
                            (catalog.ByPath[freezePath], freeze, eventHash))
                        || !caseIds.Add(freeze.CaseId))
                    {
                        throw new FormatException("Frozen module path or case ID was reused.");
                    }

                    freezeOrder.Add(("active-frozen", freeze.CaseId));
                    events.Add(new FrozenLedgerEvent.Freeze(sequence, eventHash, previousHash, freeze));
                }
                else if (string.Equals(eventType, "Genesis", StringComparison.Ordinal))
                {
                    throw new FormatException("Genesis may occur only once at sequence zero.");
                }
                else if (eventType is SupersedeEventType or "Revoke")
                {
                    throw new FormatException($"{eventType} requires candidate-prefix validation and cannot occur in Genesis.");
                }
                else
                {
                    throw new FormatException($"Unknown frozen event type {eventType}.");
                }

                previous = eventHash;
            }

            var canonicalFreezeOrder = freezeOrder
                .OrderBy(static item => item.CaseClass, StringComparer.Ordinal)
                .ThenBy(static item => item.CaseId, StringComparer.Ordinal);
            if (!freezeOrder.SequenceEqual(canonicalFreezeOrder))
            {
                throw new FormatException("Genesis Freeze events are not in canonical ordinal order.");
            }

            var expectedPaths = catalog.ClosedNodes.Select(static node => node.RepoPath).ToImmutableHashSet();
            if (!freezes.Keys.ToImmutableHashSet().SetEquals(expectedPaths))
            {
                var missing = expectedPaths.Except(freezes.Keys)
                    .OrderBy(static path => path.Value, StringComparer.Ordinal)
                    .Select(static path => path.Value);
                throw new FormatException("Closed modules are missing Freeze events: " + string.Join(", ", missing));
            }

            var active = freezes.Values
                .Select(static item => item.Material)
                .OrderBy(static node => node.RepoPath.Value, StringComparer.Ordinal)
                .ToImmutableArray();
            var corpusRoot = ComputeCorpusRoot(
                previous,
                freezes.Values.Select(static item => item.Payload).ToImmutableArray());
            var activeEntries = freezes.Values.ToImmutableDictionary(
                static item => item.Payload.CaseId,
                static item => new FrozenActiveEntry(
                    item.Material,
                    item.Payload,
                    item.LastAttestationEventHash),
                StringComparer.Ordinal);
            return new FrozenLedgerValidationOutcome.Accepted(FrozenLedgerConsistent.Create(
                syntax.RawBytes,
                events.MoveToImmutable(),
                active,
                previous,
                corpusRoot,
                ComputeFrozenGraphRoot(catalog.ClosedNodes),
                activeEntries,
                caseIds.ToImmutableHashSet(StringComparer.Ordinal),
                ImmutableHashSet<FrozenNodeId>.Empty,
                ImmutableHashSet<FrozenNodeId>.Empty));
        }
        catch (Exception exception) when (exception is FormatException or JsonException or InvalidOperationException)
        {
            return new FrozenLedgerValidationOutcome.Rejected(exception.Message);
        }
    }

}
