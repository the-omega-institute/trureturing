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
            requireCompleteCatalog: true,
            allowPendingReattestation: false,
            allowPendingEnvironmentRecoordinate: false);

    internal static FrozenLedgerValidationOutcome ValidateHistoryPrefix(
        FrozenLedgerSyntax syntax,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences trustedReferences) =>
        ValidateHistory(
            syntax,
            catalog,
            trustedReferences,
            requireCompleteCatalog: false,
            allowPendingReattestation: true,
            allowPendingEnvironmentRecoordinate: false);

    internal static FrozenLedgerValidationOutcome ValidateHistoryForEnvironmentRecoordinate(
        FrozenLedgerSyntax syntax,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences trustedReferences) =>
        ValidateHistory(
            syntax,
            catalog,
            trustedReferences,
            requireCompleteCatalog: false,
            allowPendingReattestation: true,
            allowPendingEnvironmentRecoordinate: true);

    private static FrozenLedgerValidationOutcome ValidateHistory(
        FrozenLedgerSyntax syntax,
        FrozenMaterialCatalog catalog,
        TrustedFrozenGitReferences trustedReferences,
        bool requireCompleteCatalog,
        bool allowPendingReattestation,
        bool allowPendingEnvironmentRecoordinate)
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
                    if (!allCaseIds.Add(freeze.CaseId)
                        || !activePaths.Add(freeze.NodePath))
                    {
                        throw new FormatException("Frozen history reused a case ID or active module path.");
                    }

                    active.Add(
                        freeze.CaseId,
                        new FrozenActiveEntry(
                            HistoricalMaterial(freeze),
                            freeze,
                            eventHash,
                            AxiomClosureKnown: false));
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
                        var frozenNodeId = reattest.FrozenNodeId
                            ?? throw new FormatException("Extended Reattest is missing frozen_node_id.");
                        var statementId = reattest.StatementId
                            ?? throw new FormatException("Extended Reattest is missing statement_id.");
                        var witnessId = reattest.WitnessId
                            ?? throw new FormatException("Extended Reattest is missing witness_id.");
                        active[reattest.CaseId] = entry with
                        {
                            Material = new FrozenNodeMaterial(
                                entry.Material.RepoPath,
                                reattest.DeclarationStatementIds,
                                statementId,
                                witnessId,
                                frozenNodeId,
                                reattest.PrerequisiteFrozenNodeIds,
                                entry.Material.AxiomClosure,
                                new FrozenModuleAttestation(
                                    entry.Material.RepoPath,
                                    reattest.Input.DescriptorBlobOid)
                                {
                                    BaseCommitOid = reattest.Input.BaseCommitOid,
                                    BaseTreeOid = reattest.Input.BaseTreeOid,
                                }),
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
                        candidateCatalog: null);
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
                var environmentMatches = entry.Environment is null
                    || EnvironmentMatches(entry.Environment, catalog.Environment);
                if (materialMatches && environmentMatches)
                {
                    active[caseId] = entry with { Material = material };
                    continue;
                }

                if (allowPendingEnvironmentRecoordinate)
                {
                    continue;
                }

                if (entry.Payload.StatementId != material.StatementId
                    || !entry.Payload.DeclarationStatementIds.SequenceEqual(
                        material.DeclarationStatementIds))
                {
                    throw new HistoryFinalStateException(
                        ImmutableArray.Create(material.RepoPath),
                        $"Active module {material.RepoPath.Value} statement identity changed; append Revoke before the replacement Freeze.");
                }

                if (allowPendingReattestation)
                {
                    continue;
                }

                if (!environmentMatches)
                {
                    throw new HistoryFinalStateException(
                        ImmutableArray.Create(material.RepoPath),
                        $"Active module {material.RepoPath.Value} environment pins changed; run ledger-recoordinate before ledger-append.");
                }

                throw new HistoryFinalStateException(
                    ImmutableArray.Create(material.RepoPath),
                    $"Active module {material.RepoPath.Value} has material/blob drift and lacks a matching Reattest event; run ledger-append to close it with Reattest in the same transaction.");
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

    private static FrozenFreezePayload ParseHistoricalFreeze(
        JsonElement payload,
        TrustedFrozenGitReferences trustedReferences)
    {
        RequireObjectFields(
            payload,
            "Freeze payload",
            "case_class", "case_id", "declaration_statement_ids", "evaluation", "expected",
            "frozen_node_id", "input", "input_fingerprint", "node_path", "prerequisite_frozen_node_ids",
            "semantic_receipt", "statement_id", "truth_state", "witness_id");
        var pathText = RequiredString(payload, "node_path");
        if (!RepoPath.TryCreate(pathText, out var path))
        {
            throw new FormatException($"Freeze has invalid node_path {pathText}.");
        }

        var statement = ParseStatementId(RequiredString(payload, "statement_id"), "Freeze statement");
        var witness = ParseWitnessId(RequiredString(payload, "witness_id"), "Freeze witness");
        var frozen = ParseFrozenNodeId(RequiredString(payload, "frozen_node_id"), "Freeze node");
        var result = new FrozenFreezePayload(
            RequiredString(payload, "case_class"),
            RequiredString(payload, "case_id"),
            ParseDeclarationStatementIds(payload),
            RequiredString(payload, "evaluation"),
            ParseExpected(payload.GetProperty("expected")),
            frozen,
            ParseInput(payload.GetProperty("input")),
            RequiredString(payload, "input_fingerprint"),
            path,
            ParseFrozenNodeIds(payload, "prerequisite_frozen_node_ids"),
            RequiredString(payload, "semantic_receipt"),
            statement,
            RequiredString(payload, "truth_state"),
            witness);
        if (!trustedReferences.Covers(result.Input))
        {
            throw new FormatException("Historical Freeze input has no validated Git commit/tree/blob capability.");
        }
        if (result.CaseClass != "active-frozen"
            || result.CaseId != FrozenLedgerCanonicalWriter.CaseId(frozen)
            || result.Evaluation != "admission"
            || result.TruthState != nameof(TruthState.Closed)
            || !result.Expected.AllowedDispositions.SequenceEqual(new[] { "admit" }, StringComparer.Ordinal)
            || result.Expected.DiagnosticMatch != "none"
            || result.Expected.RequiredDiagnostics.Length != 0
            || result.InputFingerprint != witness.Value
            || result.SemanticReceipt != frozen.Value
            || result.Input.DescriptorSelector != path.Value
            || result.Input.Materializer != "repository-snapshot-v1")
        {
            throw new FormatException($"Historical Freeze payload is not a canonical Closed module at {path.Value}.");
        }

        return result;
    }

    private static FrozenNodeMaterial HistoricalMaterial(FrozenFreezePayload payload) => new(
        payload.NodePath,
        payload.DeclarationStatementIds,
        payload.StatementId,
        payload.WitnessId,
        payload.FrozenNodeId,
        payload.PrerequisiteFrozenNodeIds,
        ImmutableArray<string>.Empty,
        new FrozenModuleAttestation(payload.NodePath, payload.Input.DescriptorBlobOid));

    private static bool HistoricalActiveFreezeMatches(
        FrozenFreezePayload payload,
        FrozenNodeMaterial material) =>
        payload.DeclarationStatementIds.SequenceEqual(material.DeclarationStatementIds)
        && payload.StatementId == material.StatementId
        && payload.WitnessId == material.WitnessId
        && payload.FrozenNodeId == material.FrozenNodeId
        && payload.PrerequisiteFrozenNodeIds.SequenceEqual(material.PrerequisiteFrozenNodeIds)
        && payload.Input.DescriptorBlobOid == material.Attestation.SourceBlobOid
        && payload.Input.DescriptorSelector == material.RepoPath.Value;

    private static bool EnvironmentMatches(
        FrozenEnvironmentPins actual,
        FrozenEnvironmentAttestation expected) =>
        actual.LeanToolchainBlobOid == expected.LeanToolchainBlobOid
        && actual.LakeManifestBlobOid == expected.LakeManifestBlobOid
        && actual.LakefilePath.Value == expected.LakefilePath
        && actual.LakefileBlobOid == expected.LakefileBlobOid;

    private static StatementId ParseStatementId(string value, string label) =>
        FrozenHashSyntax.IsSha256(value)
            ? StatementId.Create(value)
            : throw new FormatException($"{label} is malformed.");

    private static WitnessId ParseWitnessId(string value, string label) =>
        FrozenHashSyntax.IsSha256(value)
            ? WitnessId.Create(value)
            : throw new FormatException($"{label} is malformed.");
}
