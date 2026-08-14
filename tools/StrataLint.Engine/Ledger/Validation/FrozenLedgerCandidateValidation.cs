using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

public static partial class FrozenLedger
{
    public static FrozenLedgerValidationOutcome ValidateCandidate(
        FrozenLedgerSyntax syntax,
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences trustedReferences) =>
        ValidateCandidate(
            syntax,
            baseline,
            catalog,
            trustedReferences,
            TrustedRevocationReceiptStore.Empty(baseline));

    public static FrozenLedgerValidationOutcome ValidateCandidate(
        FrozenLedgerSyntax syntax,
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences trustedReferences,
        TrustedRevocationReceiptStore trustedRevocationReceipts)
    {
        ArgumentNullException.ThrowIfNull(syntax);
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(catalog);
        ArgumentNullException.ThrowIfNull(trustedReferences);
        ArgumentNullException.ThrowIfNull(trustedRevocationReceipts);
        try
        {
            ValidateSyntaxEnvelope(syntax);
            if (!syntax.RawBytes.AsSpan().StartsWith(baseline.RawBytes.AsSpan()))
            {
                throw new FormatException(
                    "Candidate frozen ledger does not retain the exact baseline byte prefix.");
            }

            if (syntax.Lines.Length < baseline.Events.Length)
            {
                throw new FormatException("Candidate frozen ledger truncated the baseline event prefix.");
            }

            var events = baseline.Events.ToBuilder();
            var active = baseline.ActiveEntries.ToDictionary(static item => item.Key, static item => item.Value, StringComparer.Ordinal);
            var allCaseIds = baseline.AllCaseIds.ToHashSet(StringComparer.Ordinal);
            var revoked = baseline.RevokedFrozenNodeIds.ToHashSet();
            var activePathCases = active.Values.ToDictionary(
                static item => item.Material.RepoPath,
                static item => item.Payload.CaseId);
            var previous = baseline.HeadHash;
            for (var index = baseline.Events.Length; index < syntax.Lines.Length; index++)
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
                    || !string.Equals(previousHash, previous, StringComparison.Ordinal)
                    || !FrozenHashSyntax.IsSha256(eventHash)
                    || !string.Equals(eventHash, ComputeEventHash(root), StringComparison.Ordinal))
                {
                    throw new FormatException("Candidate suffix has an invalid sequence/hash chain.");
                }

                var eventType = RequiredString(root, "event_type");
                var payload = root.GetProperty("payload");
                if (eventType == "Freeze")
                {
                    var freeze = ParseFreeze(payload, catalog, trustedReferences);
                    if (!allCaseIds.Add(freeze.CaseId)
                        || activePathCases.ContainsKey(freeze.NodePath))
                    {
                        throw new FormatException(
                            "Freeze reused a historical case ID or an active module path; correction requires Revoke first.");
                    }

                    var material = catalog.ByPath[freeze.NodePath];
                    active.Add(
                        freeze.CaseId,
                        new FrozenActiveEntry(material, freeze, eventHash));
                    activePathCases.Add(freeze.NodePath, freeze.CaseId);
                    events.Add(new FrozenLedgerEvent.Freeze(sequence, eventHash, previousHash, freeze));
                }
                else if (eventType == "Reattest")
                {
                    var reattest = ParseReattest(payload, active, trustedReferences);
                    var entry = active[reattest.CaseId];
                    if (reattest.IsLegacyFormat)
                    {
                        active[reattest.CaseId] = entry with
                        {
                            Payload = entry.Payload with
                            {
                                Input = reattest.Input,
                                InputFingerprint = reattest.InputFingerprint,
                                SemanticReceipt = reattest.SemanticReceipt,
                            },
                            LastAttestationEventHash = eventHash,
                        };
                    }
                    else
                    {
                        if (!catalog.ByPath.TryGetValue(entry.Material.RepoPath, out var material))
                        {
                            throw new FormatException(
                                $"Reattest target {entry.Material.RepoPath.Value} is no longer Closed.");
                        }

                        ValidateReattestMaterial(reattest, material);
                        var frozenNodeId = reattest.FrozenNodeId
                            ?? throw new FormatException("Extended Reattest is missing frozen_node_id.");
                        var statementId = reattest.StatementId
                            ?? throw new FormatException("Extended Reattest is missing statement_id.");
                        var witnessId = reattest.WitnessId
                            ?? throw new FormatException("Extended Reattest is missing witness_id.");
                        active[reattest.CaseId] = entry with
                        {
                            Material = material,
                            Payload = entry.Payload with
                            {
                                DeclarationStatementIds = reattest.DeclarationStatementIds,
                                FrozenNodeId = frozenNodeId,
                                Input = reattest.Input,
                                InputFingerprint = reattest.InputFingerprint,
                                PrerequisiteFrozenNodeIds = reattest.PrerequisiteFrozenNodeIds,
                                SemanticReceipt = reattest.SemanticReceipt,
                                StatementId = statementId,
                                WitnessId = witnessId,
                            },
                            LastAttestationEventHash = eventHash,
                        };
                    }

                    events.Add(new FrozenLedgerEvent.Reattest(
                        sequence,
                        eventHash,
                        previousHash,
                        reattest));
                }
                else if (eventType == EnvironmentRecoordinateEventType)
                {
                    var recoordinate = ValidateEnvironmentRecoordinate(
                        payload,
                        active,
                        trustedReferences,
                        catalog);
                    active[recoordinate.CaseId] = ApplyEnvironmentRecoordinate(
                        active[recoordinate.CaseId],
                        recoordinate,
                        eventHash);
                    events.Add(new FrozenLedgerEvent.EnvironmentRecoordinate(
                        sequence,
                        eventHash,
                        previousHash,
                        recoordinate));
                }
                else if (eventType == "Revoke")
                {
                    var revoke = ParseRevoke(
                        payload,
                        baseline,
                        active,
                        trustedRevocationReceipts);
                    foreach (var caseId in revoke.AffectedCaseIds)
                    {
                        var entry = active[caseId];
                        active.Remove(caseId);
                        activePathCases.Remove(entry.Material.RepoPath);
                        revoked.Add(entry.Material.FrozenNodeId);
                    }

                    events.Add(new FrozenLedgerEvent.Revoke(
                        sequence,
                        eventHash,
                        previousHash,
                        revoke));
                }
                else
                {
                    throw new FormatException($"Event type {eventType} is not legal in a candidate suffix.");
                }

                previous = eventHash;
            }

            var expected = catalog.ClosedNodes.ToDictionary(static node => node.RepoPath);
            var actual = active.Values.ToDictionary(static entry => entry.Material.RepoPath);
            var missing = expected.Keys.Except(actual.Keys)
                .OrderBy(static path => path.Value, StringComparer.Ordinal)
                .Select(static path => path.Value)
                .ToArray();
            if (missing.Length > 0)
            {
                throw new FormatException("Closed modules are missing Freeze events: " + string.Join(", ", missing));
            }

            if (actual.Count != expected.Count
                || expected.Any(item => actual[item.Key].Material.FrozenNodeId != item.Value.FrozenNodeId))
            {
                throw new FormatException(
                    "Active frozen view does not exactly match the current Closed module identities.");
            }

            var activeNodes = active.Values
                .Select(static entry => entry.Material)
                .OrderBy(static node => node.RepoPath.Value, StringComparer.Ordinal)
                .ToImmutableArray();
            var activeEntries = active.ToImmutableDictionary(StringComparer.Ordinal);
            var corpusRoot = ComputeCorpusRoot(
                previous,
                activeEntries.Values.Select(static entry => entry.Payload).ToImmutableArray());
            return new FrozenLedgerValidationOutcome.Accepted(FrozenLedgerConsistent.Create(
                syntax.RawBytes,
                events.ToImmutable(),
                activeNodes,
                previous,
                corpusRoot,
                ComputeFrozenGraphRoot(catalog.ClosedNodes),
                activeEntries,
                allCaseIds.ToImmutableHashSet(StringComparer.Ordinal),
                revoked.ToImmutableHashSet()));
        }
        catch (Exception exception) when (exception is FormatException or JsonException or InvalidOperationException)
        {
            return new FrozenLedgerValidationOutcome.Rejected(exception.Message);
        }
    }

    private static FrozenReattestPayload ParseReattest(
        JsonElement payload,
        IReadOnlyDictionary<string, FrozenActiveEntry> active,
        TrustedFrozenGitReferences trustedReferences)
    {
        if (HasExactObjectFields(
            payload,
            "case_id", "input", "input_fingerprint", "previous_attestation_event_hash", "semantic_receipt"))
        {
            return ParseLegacyReattest(payload, active, trustedReferences);
        }

        return ParseExtendedReattest(payload, active, trustedReferences);
    }

    private static FrozenReattestPayload ParseLegacyReattest(
        JsonElement payload,
        IReadOnlyDictionary<string, FrozenActiveEntry> active,
        TrustedFrozenGitReferences trustedReferences)
    {
        RequireObjectFields(
            payload,
            "Reattest payload",
            "case_id", "input", "input_fingerprint", "previous_attestation_event_hash", "semantic_receipt");
        var result = new FrozenReattestPayload(
            RequiredString(payload, "case_id"),
            ParseInput(payload.GetProperty("input")),
            RequiredString(payload, "input_fingerprint"),
            RequiredString(payload, "previous_attestation_event_hash"),
            RequiredString(payload, "semantic_receipt"));
        if (!trustedReferences.Covers(result.Input))
        {
            throw new FormatException("Reattest input has no validated Git commit/tree/blob capability.");
        }
        if (!active.TryGetValue(result.CaseId, out var entry)
            || result.PreviousAttestationEventHash != entry.LastAttestationEventHash
            || result.InputFingerprint != entry.Payload.InputFingerprint
            || result.SemanticReceipt != entry.Payload.SemanticReceipt)
        {
            throw new FormatException(
                "Reattest targets an inactive/unknown case or changes semantic identity.");
        }

        if (result.Input.DescriptorBlobOid != entry.Payload.Input.DescriptorBlobOid
            || result.Input.DescriptorSelector != entry.Payload.Input.DescriptorSelector
            || result.Input.Materializer != entry.Payload.Input.Materializer
            || !result.Input.SupportingBlobOids.SequenceEqual(entry.Payload.Input.SupportingBlobOids))
        {
            throw new FormatException(
                "Reattest changed semantic attestation material without an equivalence proof.");
        }

        return result;
    }

    private static FrozenReattestPayload ParseExtendedReattest(
        JsonElement payload,
        IReadOnlyDictionary<string, FrozenActiveEntry> active,
        TrustedFrozenGitReferences trustedReferences)
    {
        RequireObjectFields(
            payload,
            "Reattest payload",
            "case_id", "declaration_statement_ids", "frozen_node_id", "input", "input_fingerprint",
            "prerequisite_frozen_node_ids", "previous_attestation_event_hash", "semantic_receipt",
            "statement_id", "witness_id");
        var result = new FrozenReattestPayload(
            RequiredString(payload, "case_id"),
            ParseDeclarationStatementIds(payload),
            ParseFrozenNodeId(RequiredString(payload, "frozen_node_id"), "Reattest node"),
            ParseInput(payload.GetProperty("input")),
            RequiredString(payload, "input_fingerprint"),
            ParseFrozenNodeIds(payload, "prerequisite_frozen_node_ids"),
            RequiredString(payload, "previous_attestation_event_hash"),
            RequiredString(payload, "semantic_receipt"),
            ParseStatementId(RequiredString(payload, "statement_id"), "Reattest statement"),
            ParseWitnessId(RequiredString(payload, "witness_id"), "Reattest witness"));
        if (!trustedReferences.Covers(result.Input))
        {
            throw new FormatException("Reattest input has no validated Git commit/tree/blob capability.");
        }

        var statementId = result.StatementId
            ?? throw new FormatException("Extended Reattest is missing statement_id.");
        var witnessId = result.WitnessId
            ?? throw new FormatException("Extended Reattest is missing witness_id.");
        var frozenNodeId = result.FrozenNodeId
            ?? throw new FormatException("Extended Reattest is missing frozen_node_id.");
        if (!active.TryGetValue(result.CaseId, out var entry)
            || result.PreviousAttestationEventHash != entry.LastAttestationEventHash
            || statementId != entry.Payload.StatementId
            || !result.DeclarationStatementIds.SequenceEqual(entry.Payload.DeclarationStatementIds))
        {
            throw new FormatException(
                "Reattest targets an inactive/unknown case or changes statement identity.");
        }

        if (result.InputFingerprint != witnessId.Value
            || result.SemanticReceipt != frozenNodeId.Value
            || result.Input.DescriptorSelector != entry.Payload.Input.DescriptorSelector
            || result.Input.Materializer != entry.Payload.Input.Materializer
            || !result.Input.SupportingBlobOids.SequenceEqual(entry.Payload.Input.SupportingBlobOids))
        {
            throw new FormatException(
                "Reattest payload is not a canonical attestation of the same statement.");
        }

        return result;
    }

    private static void ValidateReattestMaterial(
        FrozenReattestPayload payload,
        FrozenNodeMaterial material)
    {
        if (!payload.IsExtendedFormat
            || !payload.DeclarationStatementIds.SequenceEqual(material.DeclarationStatementIds)
            || payload.StatementId != material.StatementId
            || payload.WitnessId != material.WitnessId
            || payload.FrozenNodeId != material.FrozenNodeId
            || !payload.PrerequisiteFrozenNodeIds.SequenceEqual(material.PrerequisiteFrozenNodeIds)
            || payload.Input.DescriptorBlobOid != material.Attestation.SourceBlobOid
            || payload.Input.DescriptorSelector != material.RepoPath.Value)
        {
            throw new FormatException(
                $"Reattest does not match recomputed material for {material.RepoPath.Value}.");
        }
    }

    private static FrozenRevokePayload ParseRevoke(
        JsonElement payload,
        FrozenLedgerConsistent baseline,
        IReadOnlyDictionary<string, FrozenActiveEntry> active,
        TrustedRevocationReceiptStore trustedReceipts)
    {
        RequireObjectFields(
            payload,
            "Revoke payload",
            "affected_case_ids", "affected_frozen_node_ids", "closure_hash", "evidence",
            "graph_root", "root_case_ids", "root_frozen_node_ids");
        var affectedCases = RequiredStringArray(payload, "affected_case_ids");
        var affectedIds = ParseFrozenNodeIds(payload, "affected_frozen_node_ids");
        var rootCases = RequiredStringArray(payload, "root_case_ids");
        var rootIds = ParseFrozenNodeIds(payload, "root_frozen_node_ids");
        var evidenceElement = payload.GetProperty("evidence");
        if (evidenceElement.ValueKind != JsonValueKind.Array)
        {
            throw new FormatException("Revoke evidence must be an array.");
        }

        var evidence = evidenceElement.EnumerateArray().Select(ParseEvidence).ToImmutableArray();
        var evidenceKeys = evidence.Select(EvidenceSortKey).ToArray();
        if (!evidenceKeys.SequenceEqual(evidenceKeys.Order(StringComparer.Ordinal), StringComparer.Ordinal))
        {
            throw new FormatException("Revoke evidence must be ordinal-sorted by root and variant.");
        }

        var validated = evidence.Select(item =>
            RevocationEvidenceValidator.Validate(
                item,
                baseline,
                trustedReceipts) switch
            {
                RevocationEvidenceValidationOutcome.Accepted accepted => accepted.Capability,
                RevocationEvidenceValidationOutcome.Rejected rejected =>
                    throw new FormatException(rejected.Message),
            }).ToImmutableArray();
        var planned = RevocationPlanner.Plan(
            baseline,
            validated) switch
        {
            RevocationPlanOutcome.Accepted accepted => accepted.Capability,
            RevocationPlanOutcome.Rejected rejected => throw new FormatException(rejected.Message),
        };
        var rootSet = planned.RootFrozenNodeIds.ToHashSet();
        var expectedRootCases = active.Values
            .Where(entry => rootSet.Contains(entry.Material.FrozenNodeId))
            .Select(static entry => entry.Payload.CaseId)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var closureHash = RequiredString(payload, "closure_hash");
        var graphRoot = RequiredString(payload, "graph_root");
        if (!FrozenHashSyntax.IsSha256(closureHash)
            || !FrozenHashSyntax.IsSha256(graphRoot)
            || closureHash != planned.ClosureHash
            || graphRoot != baseline.GraphRoot
            || !rootIds.SequenceEqual(planned.RootFrozenNodeIds)
            || !rootCases.SequenceEqual(expectedRootCases, StringComparer.Ordinal)
            || !affectedIds.SequenceEqual(planned.AffectedFrozenNodeIds)
            || !affectedCases.SequenceEqual(planned.AffectedCaseIds, StringComparer.Ordinal))
        {
            throw new FormatException(
                "Revoke roots, evidence, graph, affected set, or closure hash does not match Engine recomputation.");
        }

        if (planned.AffectedCaseIds.Any(caseId => !active.ContainsKey(caseId)))
        {
            throw new FormatException("Revoke closure contains a case already inactive in the candidate suffix.");
        }

        return new FrozenRevokePayload(
            affectedCases,
            affectedIds,
            closureHash,
            evidence,
            graphRoot,
            rootCases,
            rootIds);
    }

}
