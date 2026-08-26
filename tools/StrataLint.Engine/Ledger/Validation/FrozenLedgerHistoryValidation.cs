using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

public static partial class FrozenLedger
{
    private sealed class HistoryFinalStateException(
        ImmutableArray<RepoPath> paths,
        string message) : FormatException(message)
    {
        internal ImmutableArray<RepoPath> Paths { get; } = paths;
    }

    public static FrozenLedgerValidationOutcome ValidateHistory(
        FrozenLedgerSyntax syntax,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences trustedReferences) =>
        ValidateHistory(
            syntax,
            catalog,
            trustedReferences,
            requireCompleteCatalog: true);

    internal static FrozenLedgerValidationOutcome ValidateHistoryPrefix(
        FrozenLedgerSyntax syntax,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences trustedReferences) =>
        ValidateHistory(
            syntax,
            catalog,
            trustedReferences,
            requireCompleteCatalog: false);

    private static FrozenLedgerValidationOutcome ValidateHistory(
        FrozenLedgerSyntax syntax,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences trustedReferences,
        bool requireCompleteCatalog)
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
            var active = new Dictionary<string, FrozenActiveEntry>(StringComparer.Ordinal);
            var activePaths = new HashSet<RepoPath>();
            var allCaseIds = new HashSet<string>(StringComparer.Ordinal);
            var superseded = new HashSet<FrozenNodeId>();
            var revoked = new HashSet<FrozenNodeId>();
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
                    throw new FormatException("Frozen history has an invalid sequence/hash chain.");
                }

                var eventType = RequiredString(root, "event_type");
                var payload = root.GetProperty("payload");
                if (index == 0)
                {
                    if (eventType != "Genesis")
                    {
                        throw new FormatException("Sequence zero must be Genesis.");
                    }

                    events.Add(new FrozenLedgerEvent.Genesis(
                        sequence,
                        eventHash,
                        previousHash,
                        ParseHistoricalGenesis(payload, catalog)));
                }
                else if (eventType == "Freeze")
                {
                    var freeze = ParseHistoricalFreeze(payload, trustedReferences);
                    var freezePath = RepoPath.CreateKnown(freeze.Input.DescriptorSelector);
                    if (!allCaseIds.Add(freeze.CaseId)
                        || !activePaths.Add(freezePath))
                    {
                        throw new FormatException("Frozen history reused a case ID or active module path.");
                    }

                    active.Add(
                        freeze.CaseId,
                        new FrozenActiveEntry(
                            HistoricalMaterial(freeze),
                            freeze,
                            eventHash,
                            AxiomClosureKnown: freeze.HasAxiomClosure));
                    events.Add(new FrozenLedgerEvent.Freeze(sequence, eventHash, previousHash, freeze));
                }
                else if (eventType == SupersedeEventType)
                {
                    var supersede = ValidateSupersede(
                        payload,
                        active,
                        trustedReferences,
                        candidateCatalog: null,
                        repositoryImportClosureUnchanged: false,
                        externalImportsCoveredByNamedPins: true,
                        relevantSemanticPinsChanged: false,
                        candidateStatementsAvoidTrivialTruth: true);
                    var oldEntry = active[supersede.CaseId];
                    superseded.Add(oldEntry.Material.FrozenNodeId);
                    active[supersede.CaseId] = ApplySupersede(
                        oldEntry,
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
                    var revoke = ParseHistoricalRevoke(payload, events, active, previous);
                    foreach (var caseId in revoke.AffectedCaseIds)
                    {
                        var entry = active[caseId];
                        active.Remove(caseId);
                        activePaths.Remove(entry.Material.RepoPath);
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
                    throw new FormatException($"Unknown frozen event type {eventType}.");
                }

                previous = eventHash;
            }

            var expectedByPath = catalog.ClosedNodes.ToDictionary(static node => node.RepoPath);
            var actualByPath = active.Values.ToDictionary(static entry => entry.Material.RepoPath);
            var missing = expectedByPath.Keys.Except(actualByPath.Keys)
                .OrderBy(static path => path.Value, StringComparer.Ordinal)
                .ToImmutableArray();
            if (requireCompleteCatalog && missing.Length > 0)
            {
                throw new HistoryFinalStateException(
                    missing,
                    "Closed modules are missing Freeze events: "
                    + string.Join(", ", missing.Select(static path => path.Value))
                    + "; run ledger-append to append the missing Freeze events.");
            }

            var outside = actualByPath.Keys.Except(expectedByPath.Keys)
                .OrderBy(static path => path.Value, StringComparer.Ordinal)
                .ToImmutableArray();
            if (outside.Length > 0)
            {
                throw new HistoryFinalStateException(
                    outside,
                    "Active frozen history contains modules outside the current Closed catalog: "
                    + string.Join(", ", outside.Select(static path => path.Value))
                    + "; append Revoke before replacing or removing their Freeze events.");
            }

            foreach (var (caseId, entry) in active.OrderBy(
                static item => item.Value.Material.RepoPath.Value,
                StringComparer.Ordinal).ToArray())
            {
                var material = expectedByPath[entry.Material.RepoPath];
                var materialMatches = HistoricalActiveFreezeMatches(entry.Payload, material);
                if (materialMatches)
                {
                    active[caseId] = entry with { Material = material };
                    continue;
                }

                if (entry.Payload.StatementId != material.StatementId
                    || !entry.Payload.DeclarationStatementIds.SequenceEqual(
                        material.DeclarationStatementIds))
                {
                    throw new HistoryFinalStateException(
                        ImmutableArray.Create(material.RepoPath),
                        $"Active module {material.RepoPath.Value} statement identity changed; append Revoke before rerunning ledger-append.");
                }

                throw new HistoryFinalStateException(
                    ImmutableArray.Create(material.RepoPath),
                    $"Active module {material.RepoPath.Value} changed identity; append Revoke before rerunning ledger-append.");
            }

            var activeEntries = active.ToImmutableDictionary(StringComparer.Ordinal);
            var activeNodes = activeEntries.Values
                .Select(static entry => entry.Material)
                .OrderBy(static node => node.RepoPath.Value, StringComparer.Ordinal)
                .ToImmutableArray();
            return new FrozenLedgerValidationOutcome.Accepted(FrozenLedgerConsistent.Create(
                syntax.RawBytes,
                events.MoveToImmutable(),
                activeNodes,
                previous,
                ComputeCorpusRoot(
                    previous,
                    activeEntries.Values.Select(static entry => entry.Payload).ToImmutableArray()),
                ComputeFrozenGraphRoot(activeNodes),
                activeEntries,
                allCaseIds.ToImmutableHashSet(StringComparer.Ordinal),
                superseded.ToImmutableHashSet(),
                revoked.ToImmutableHashSet()));
        }
        catch (Exception exception) when (
            exception is FormatException or JsonException or InvalidOperationException or KeyNotFoundException)
        {
            var rejected = new FrozenLedgerValidationOutcome.Rejected(exception.Message);
            return exception is HistoryFinalStateException finalState
                ? rejected with
                {
                    HistoryFailurePaths = finalState.Paths,
                }
                : rejected;
        }
    }

    internal static FrozenRevokePayload ReadTrustedRevoke(JsonElement payload)
    {
        var evidence = payload.GetProperty("evidence");
        if (evidence.ValueKind != JsonValueKind.Array)
        {
            throw new FormatException("trusted Revoke evidence is not an array");
        }

        return new FrozenRevokePayload(
            RequiredStringArray(payload, "affected_case_ids"),
            ParseFrozenNodeIds(payload, "affected_frozen_node_ids"),
            RequiredString(payload, "closure_hash"),
            evidence.EnumerateArray().Select(ParseEvidence).ToImmutableArray(),
            RequiredString(payload, "graph_root"),
            RequiredStringArray(payload, "root_case_ids"));
    }

    private static FrozenFreezePayload ParseHistoricalFreeze(
        JsonElement payload,
        TrustedFrozenGitReferences trustedReferences)
    {
        RequireEventPayloadFields(payload, "Freeze");
        var currentShape = HasExactObjectFields(
            payload,
            FrozenLedgerReferenceProjection.FreezePayloadFieldsV4);
        var input = ParseInput(payload.GetProperty("input"));
        var pathText = currentShape
            ? input.DescriptorSelector
            : RequiredString(payload, "node_path");
        if (!RepoPath.TryCreate(pathText, out var path))
        {
            throw new FormatException($"Freeze has invalid node_path {pathText}.");
        }

        var statement = ParseStatementId(RequiredString(payload, "statement_id"), "Freeze statement");
        var witness = ParseWitnessId(RequiredString(payload, "witness_id"), "Freeze witness");
        var frozen = ParseFrozenNodeId(RequiredString(payload, "frozen_node_id"), "Freeze node");
        var result = new FrozenFreezePayload(
            RequiredString(payload, "case_id"),
            ParseDeclarationStatementIds(payload),
            frozen,
            input,
            ParseFrozenNodeIds(payload, "prerequisite_frozen_node_ids"),
            statement,
            witness)
        {
            AxiomClosure = ParseOptionalAxiomClosure(payload),
        };
        if (!trustedReferences.Covers(result.Input))
        {
            throw new FormatException("Historical Freeze input has no validated Git commit/tree/blob capability.");
        }
        if (!currentShape)
        {
            var expected = ParseExpected(payload.GetProperty("expected"));
            if (RequiredString(payload, "case_class") != "active-frozen"
                || RequiredString(payload, "evaluation") != "admission"
                || RequiredString(payload, "truth_state") != nameof(TruthState.Closed)
                || !expected.AllowedDispositions.SequenceEqual(new[] { "admit" }, StringComparer.Ordinal)
                || expected.DiagnosticMatch != "none"
                || expected.RequiredDiagnostics.Length != 0
                || RequiredString(payload, "input_fingerprint") != witness.Value
                || RequiredString(payload, "semantic_receipt") != frozen.Value)
            {
                throw new FormatException(
                    $"Historical Freeze payload is not a canonical Closed module at {path.Value}.");
            }
        }

        if (result.CaseId != FrozenLedgerCanonicalWriter.CaseId(frozen)
            || result.Input.DescriptorSelector != path.Value
            || result.Input.Materializer != "repository-snapshot-v1")
        {
            throw new FormatException($"Historical Freeze payload is not a canonical Closed module at {path.Value}.");
        }

        return result;
    }

    private static FrozenNodeMaterial HistoricalMaterial(FrozenFreezePayload payload) => new(
        RepoPath.CreateKnown(payload.Input.DescriptorSelector),
        payload.DeclarationStatementIds,
        payload.StatementId,
        payload.WitnessId,
        payload.FrozenNodeId,
        payload.PrerequisiteFrozenNodeIds,
        payload.HasAxiomClosure ? payload.AxiomClosure : ImmutableArray<string>.Empty,
        new FrozenModuleAttestation(
            RepoPath.CreateKnown(payload.Input.DescriptorSelector),
            payload.Input.DescriptorBlobOid));

    private static bool HistoricalActiveFreezeMatches(
        FrozenFreezePayload payload,
        FrozenNodeMaterial material) =>
        payload.DeclarationStatementIds.SequenceEqual(material.DeclarationStatementIds)
        && payload.StatementId == material.StatementId
        && payload.WitnessId == material.WitnessId
        && payload.FrozenNodeId == material.FrozenNodeId
        && payload.PrerequisiteFrozenNodeIds.SequenceEqual(material.PrerequisiteFrozenNodeIds)
        && payload.Input.DescriptorSelector == material.RepoPath.Value;

    private static StatementId ParseStatementId(string value, string label) =>
        FrozenHashSyntax.IsSha256(value)
            ? StatementId.Create(value)
            : throw new FormatException($"{label} is malformed.");

    private static WitnessId ParseWitnessId(string value, string label) =>
        FrozenHashSyntax.IsSha256(value)
            ? WitnessId.Create(value)
            : throw new FormatException($"{label} is malformed.");
}
