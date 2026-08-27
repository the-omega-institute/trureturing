using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

public static partial class FrozenLedger
{
    public static FrozenLedgerValidationOutcome ValidateCandidate(
        ImmutableArray<DagLedgerFileEvent> events,
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences trustedReferences) =>
        ValidateCandidate(
            events,
            baseline,
            catalog,
            trustedReferences,
            TrustedRevocationReceiptStore.Empty(baseline),
            requireCompleteCatalog: true);

    internal static FrozenLedgerValidationOutcome ValidateCandidatePrefix(
        ImmutableArray<DagLedgerFileEvent> events,
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences trustedReferences) =>
        ValidateCandidate(
            events,
            baseline,
            catalog,
            trustedReferences,
            TrustedRevocationReceiptStore.Empty(baseline),
            requireCompleteCatalog: false);

    public static FrozenLedgerValidationOutcome ValidateCandidate(
        ImmutableArray<DagLedgerFileEvent> events,
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences trustedReferences,
        TrustedRevocationReceiptStore trustedRevocationReceipts) =>
        ValidateCandidate(
            events,
            baseline,
            catalog,
            trustedReferences,
            trustedRevocationReceipts,
            requireCompleteCatalog: true);

    private static FrozenLedgerValidationOutcome ValidateCandidate(
        ImmutableArray<DagLedgerFileEvent> events,
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences trustedReferences,
        TrustedRevocationReceiptStore trustedRevocationReceipts,
        bool requireCompleteCatalog)
    {
        if (events.IsDefault)
        {
            throw new ArgumentException("Candidate frozen event set is uninitialized.", nameof(events));
        }
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(catalog);
        ArgumentNullException.ThrowIfNull(trustedReferences);
        ArgumentNullException.ThrowIfNull(trustedRevocationReceipts);
        try
        {
            var active = baseline.ActiveEntries.ToDictionary(static item => item.Key, static item => item.Value, StringComparer.Ordinal);
            var allCaseIds = baseline.AllCaseIds.ToHashSet(StringComparer.Ordinal);
            var revoked = baseline.RevokedFrozenNodeIds.ToHashSet();
            var activePathCases = active.Values.ToDictionary(
                static item => item.Material.RepoPath,
                static item => item.Payload.CaseId);
            var eventHashes = baseline.EventHashes.ToHashSet(StringComparer.Ordinal);
            foreach (var item in events)
            {
                if (item.SchemaVersion != FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion)
                {
                    throw new FormatException(
                        $"New accepted event must use schema_version {FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion}.");
                }

                if (!eventHashes.Add(item.EventHash))
                {
                    throw new FormatException("Candidate frozen event set duplicates an existing event hash.");
                }

                if (item.EventType == "Freeze")
                {
                    var freeze = ParseFreeze(item.Payload, catalog, trustedReferences);
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
                        new FrozenActiveEntry(material, freeze, item.EventHash));
                    activePathCases.Add(freezePath, freeze.CaseId);
                }
                else if (item.EventType == "Revoke")
                {
                    var revoke = ParseRevoke(
                        item.Payload,
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

                }
                else
                {
                    throw new FormatException(
                        $"Event type {item.EventType} is not legal in a candidate event set.");
                }
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

            if (actual.Keys.Any(path => !currentClosedPaths.Contains(path)))
            {
                throw new FormatException(
                    "Active frozen view does not exactly match the current Closed module identities.");
            }

            var recordedPathsByIdentity = FrozenPathsByIdentity(
                active.Values.Select(static entry => entry.Material));
            var currentPathsByIdentity = FrozenPathsByIdentity(
                active.Values.Select(static entry => entry.Material),
                catalog.ClosedNodes);
            foreach (var (caseId, entry) in active.ToArray())
            {
                if (!catalog.ByPath.TryGetValue(entry.Material.RepoPath, out var candidateMaterial))
                {
                    continue;
                }

                if (!FrozenLedgerHistoricalFreezeMatcher.HistoricalActiveFreezeMatches(
                    entry.Payload,
                    candidateMaterial,
                    recordedPathsByIdentity,
                    currentPathsByIdentity,
                    out _))
                {
                    throw new FormatException(
                        "Active frozen view does not exactly match the current Closed module identities.");
                }

                active[caseId] = entry with { Material = candidateMaterial };
            }

            var activeNodes = active.Values
                .Select(static entry => entry.Material)
                .OrderBy(static node => node.RepoPath.Value, StringComparer.Ordinal)
                .ToImmutableArray();
            var activeEntries = active.ToImmutableDictionary(StringComparer.Ordinal);
            var headHash = FrozenEventSetRoot.Compute(eventHashes);
            var corpusRoot = ComputeCorpusRoot(
                headHash,
                activeEntries.Values.Select(static entry => entry.Payload).ToImmutableArray());
            return new FrozenLedgerValidationOutcome.Accepted(FrozenLedgerConsistent.Create(
                activeNodes,
                headHash,
                corpusRoot,
                ComputeFrozenGraphRoot(activeNodes),
                activeEntries,
                allCaseIds.ToImmutableHashSet(StringComparer.Ordinal),
                revoked.ToImmutableHashSet(),
                eventHashes.ToImmutableHashSet(StringComparer.Ordinal),
                baseline.EventCount + events.Length));
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
