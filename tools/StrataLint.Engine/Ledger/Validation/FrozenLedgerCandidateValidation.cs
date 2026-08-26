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
            TrustedRevocationReceiptStore.Empty(baseline),
            requireCompleteCatalog: true);

    internal static FrozenLedgerValidationOutcome ValidateCandidatePrefix(
        FrozenLedgerSyntax syntax,
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences trustedReferences) =>
        ValidateCandidate(
            syntax,
            baseline,
            catalog,
            trustedReferences,
            TrustedRevocationReceiptStore.Empty(baseline),
            requireCompleteCatalog: false);

    public static FrozenLedgerValidationOutcome ValidateCandidate(
        FrozenLedgerSyntax syntax,
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences trustedReferences,
        TrustedRevocationReceiptStore trustedRevocationReceipts) =>
        ValidateCandidate(
            syntax,
            baseline,
            catalog,
            trustedReferences,
            trustedRevocationReceipts,
            requireCompleteCatalog: true);

    private static FrozenLedgerValidationOutcome ValidateCandidate(
        FrozenLedgerSyntax syntax,
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences trustedReferences,
        TrustedRevocationReceiptStore trustedRevocationReceipts,
        bool requireCompleteCatalog)
    {
        ArgumentNullException.ThrowIfNull(syntax);
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(catalog);
        ArgumentNullException.ThrowIfNull(trustedReferences);
        ArgumentNullException.ThrowIfNull(trustedRevocationReceipts);
        try
        {
            if (!syntax.RawBytes.AsSpan().StartsWith(baseline.RawBytes.AsSpan()))
            {
                throw new FormatException(
                    "Candidate frozen ledger does not retain the exact baseline byte prefix.");
            }

            var baselineLineCount = baseline.Events.Length - baseline.SyntaxStartSequence;
            if (syntax.Lines.Length < baselineLineCount)
            {
                throw new FormatException("Candidate frozen ledger truncated the baseline event prefix.");
            }

            ValidateSuffixSyntaxEnvelope(syntax, baselineLineCount);

            var events = baseline.Events.ToBuilder();
            var active = baseline.ActiveEntries.ToDictionary(static item => item.Key, static item => item.Value, StringComparer.Ordinal);
            var allCaseIds = baseline.AllCaseIds.ToHashSet(StringComparer.Ordinal);
            var superseded = baseline.SupersededFrozenNodeIds.ToHashSet();
            var supersededBaseCases = new HashSet<string>(StringComparer.Ordinal);
            var revoked = baseline.RevokedFrozenNodeIds.ToHashSet();
            var activePathCases = active.Values.ToDictionary(
                static item => item.Material.RepoPath,
                static item => item.Payload.CaseId);
            var previous = baseline.HeadHash;
            for (var index = baselineLineCount; index < syntax.Lines.Length; index++)
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
                if (sequence != baseline.SyntaxStartSequence + index
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
                    var freezePath = RepoPath.CreateKnown(freeze.Input.DescriptorSelector);
                    if (!allCaseIds.Add(freeze.CaseId)
                        || activePathCases.ContainsKey(freezePath))
                    {
                        throw new FormatException(
                            "Freeze reused a historical case ID or an active module path; correction requires Revoke first.");
                    }

                    var material = catalog.ByPath[freezePath];
                    active.Add(
                        freeze.CaseId,
                        new FrozenActiveEntry(material, freeze, eventHash));
                    activePathCases.Add(freezePath, freeze.CaseId);
                    events.Add(new FrozenLedgerEvent.Freeze(sequence, eventHash, previousHash, freeze));
                }
                else if (eventType == SupersedeEventType)
                {
                    var supersede = ValidateSupersede(
                        payload,
                        active,
                        trustedReferences,
                        catalog,
                        repositoryImportClosureUnchanged: false,
                        externalImportsCoveredByNamedPins: true,
                        relevantSemanticPinsChanged: false,
                        candidateStatementsAvoidTrivialTruth: true);
                    if (!baseline.ActiveEntries.TryGetValue(supersede.CaseId, out var baseEntry)
                        || !supersededBaseCases.Add(supersede.CaseId))
                    {
                        throw new FormatException(
                            "Supersede must target each protected-base active case at most once.");
                    }

                    superseded.Add(baseEntry.Material.FrozenNodeId);
                    active[supersede.CaseId] = ApplySupersede(
                        active[supersede.CaseId],
                        supersede,
                        eventHash);
                    events.Add(new FrozenLedgerEvent.Supersede(
                        sequence,
                        eventHash,
                        previousHash,
                        supersede));
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

            var currentClosedPaths = catalog.States
                .Where(static item => item.Value is TruthState.Closed)
                .Select(static item => item.Key)
                .ToHashSet();
            var actual = active.Values.ToDictionary(static entry => entry.Material.RepoPath);
            var missing = currentClosedPaths.Except(actual.Keys)
                .OrderBy(static path => path.Value, StringComparer.Ordinal)
                .Select(static path => path.Value)
                .ToArray();
            if (requireCompleteCatalog && missing.Length > 0)
            {
                throw new FormatException("Closed modules are missing Freeze events: " + string.Join(", ", missing));
            }

            if (actual.Keys.Any(path => !currentClosedPaths.Contains(path))
                || actual.Any(item => catalog.ByPath.TryGetValue(item.Key, out var candidateMaterial)
                    && item.Value.Material.FrozenNodeId != candidateMaterial.FrozenNodeId))
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
                ComputeFrozenGraphRoot(activeNodes),
                activeEntries,
                allCaseIds.ToImmutableHashSet(StringComparer.Ordinal),
                superseded.ToImmutableHashSet(),
                revoked.ToImmutableHashSet(),
                baseline.SyntaxStartSequence));
        }
        catch (Exception exception) when (exception is FormatException or JsonException or InvalidOperationException)
        {
            return new FrozenLedgerValidationOutcome.Rejected(exception.Message);
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
            "graph_root", "root_case_ids");
        var affectedCases = RequiredStringArray(payload, "affected_case_ids");
        var affectedIds = ParseFrozenNodeIds(payload, "affected_frozen_node_ids");
        var rootCases = RequiredStringArray(payload, "root_case_ids");
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
        var rootIds = evidence.Select(EvidenceRoot).ToImmutableArray();
        if (rootIds.Distinct().Count() != rootIds.Length)
        {
            throw new FormatException("Revoke must carry exactly one evidence item per root.");
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
            rootCases);
    }

}
