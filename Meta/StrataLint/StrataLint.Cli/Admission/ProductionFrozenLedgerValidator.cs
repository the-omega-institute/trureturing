using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class ProductionFrozenLedgerValidator
{
    internal static AdmissionOutcome? Validate(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        AcceptedLeanClosure lean,
        AcceptedLeanClosure baselineLean,
        AcyclicTruthDag dag,
        AcyclicTruthDag baselineDag,
        IRepositoryGateway repository,
        IRepositoryGateway? frozenEvidenceRepository = null)
    {
        const string path = FrozenLedgerChangeClassifier.LedgerPath;
        var baselineHasLegacy = baseline.TryGetFile(path, out var baselineFile);
        var currentHasLegacy = current.TryGetFile(path, out var currentFile);
        var baselineAccepted = AcceptedFiles(baseline);
        var currentAccepted = AcceptedFiles(current);
        var baselineHasInvalidAcceptedFiles = HasInvalidAcceptedFiles(baseline);
        var currentHasInvalidAcceptedFiles = HasInvalidAcceptedFiles(current);

        // Frozen-ledger shape timeline:
        // Before migration: legacy -> legacy validates the byte-stream ledger.
        // During migration: legacy -> accepted validates the one-time bijection.
        // After migration: accepted -> accepted validates append-only steady state.
        // Invalid: every dual, absent, mixed, or backwards shape fails closed.
        if (baselineHasLegacy && currentHasLegacy
            && baselineAccepted.Length == 0 && currentAccepted.Length == 0
            && !baselineHasInvalidAcceptedFiles && !currentHasInvalidAcceptedFiles)
        {
            return ValidateLegacy(
                current,
                baseline,
                lean,
                baselineLean,
                dag,
                baselineDag,
                repository,
                frozenEvidenceRepository,
                baselineFile!,
                currentFile!);
        }

        if (baselineHasLegacy && baselineAccepted.Length == 0
            && !currentHasLegacy && currentAccepted.Length > 0
            && !baselineHasInvalidAcceptedFiles && !currentHasInvalidAcceptedFiles)
        {
            return ValidateTransition(
                baseline,
                baselineLean,
                baselineDag,
                repository,
                frozenEvidenceRepository,
                baselineFile!,
                currentAccepted);
        }

        if (!baselineHasLegacy && baselineAccepted.Length > 0
            && !currentHasLegacy && currentAccepted.Length > 0
            && !baselineHasInvalidAcceptedFiles && !currentHasInvalidAcceptedFiles)
        {
            return ValidateSteadyState(
                current,
                baseline,
                lean,
                baselineLean,
                dag,
                baselineDag,
                repository,
                frozenEvidenceRepository,
                baselineAccepted,
                currentAccepted);
        }

        if (baselineAccepted.Length == 0 && currentAccepted.Length == 0
            && (!baselineHasLegacy || !currentHasLegacy)
            && !baselineHasInvalidAcceptedFiles && !currentHasInvalidAcceptedFiles)
        {
            return Reject("frozen ledger is missing from current or protected baseline");
        }

        // TRANSITION_REMOVAL_PREDICATE:
        // baselineAccepted.Length > 0 && !baselineHasLegacy
        // When this protected-baseline predicate is true, delete the legacy and transition branches,
        // LedgerPath, Load(bytes), the v1 writer, and transition-only tests. Keep the steady-state
        // branch as the sole accepted-only admission shape.
        return Reject("frozen ledger shape is invalid");
    }

    private static AdmissionOutcome? ValidateLegacy(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        AcceptedLeanClosure lean,
        AcceptedLeanClosure baselineLean,
        AcyclicTruthDag dag,
        AcyclicTruthDag baselineDag,
        IRepositoryGateway repository,
        IRepositoryGateway? frozenEvidenceRepository,
        RepositoryFile baselineFile,
        RepositoryFile currentFile)
    {
        var baselineLoad = DagLedgerLoader.Load(baselineFile.RawBytes.AsSpan());
        var currentLoad = DagLedgerLoader.Load(currentFile.RawBytes.AsSpan());
        if (baselineLoad is DagLedgerLoadOutcome.Invalid invalidBaseline)
        {
            return Reject("protected baseline ledger syntax is invalid: " + invalidBaseline.Message);
        }

        if (currentLoad is DagLedgerLoadOutcome.Invalid invalidCurrent)
        {
            return Reject("candidate ledger syntax is invalid: " + invalidCurrent.Message);
        }

        var baselineSyntax = ((DagLedgerLoadOutcome.Loaded)baselineLoad).Syntax;
        var currentSyntax = ((DagLedgerLoadOutcome.Loaded)currentLoad).Syntax;
        return ValidateLoaded(
            current,
            baseline,
            lean,
            baselineLean,
            dag,
            baselineDag,
            repository,
            frozenEvidenceRepository,
            baselineSyntax,
            currentSyntax);
    }

    private static AdmissionOutcome? ValidateSteadyState(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        AcceptedLeanClosure lean,
        AcceptedLeanClosure baselineLean,
        AcyclicTruthDag dag,
        AcyclicTruthDag baselineDag,
        IRepositoryGateway repository,
        IRepositoryGateway? frozenEvidenceRepository,
        ImmutableArray<RepositoryFile> baselineFiles,
        ImmutableArray<RepositoryFile> currentFiles)
    {
        if (!RetainsBaselineFilesByteForByte(baselineFiles, current))
        {
            return Reject("candidate content-addressed ledger does not retain protected baseline file byte-for-byte");
        }

        var baselineLoad = DagLedgerLoader.LoadFiles(baselineFiles);
        if (baselineLoad is DagLedgerFilesLoadOutcome.Invalid invalidBaseline)
        {
            return Reject("protected baseline content-addressed ledger is invalid: " + invalidBaseline.Message);
        }

        var currentLoad = DagLedgerLoader.LoadFiles(currentFiles);
        if (currentLoad is DagLedgerFilesLoadOutcome.Invalid invalidCurrent)
        {
            return Reject("candidate content-addressed ledger is invalid: " + invalidCurrent.Message);
        }

        var baselineEvents = ((DagLedgerFilesLoadOutcome.Loaded)baselineLoad).Events;
        var currentEvents = ((DagLedgerFilesLoadOutcome.Loaded)currentLoad).Events;
        var baselineDagFailure = DagLedgerLoader.ValidateClosedDag(baselineEvents);
        if (baselineDagFailure is not null)
        {
            return Reject("protected baseline content-addressed ledger is invalid: " + baselineDagFailure);
        }

        var currentDagFailure = DagLedgerLoader.ValidateClosedDag(currentEvents);
        if (currentDagFailure is not null)
        {
            return Reject("candidate content-addressed ledger is invalid: " + currentDagFailure);
        }

        _ = DagLedgerLoader.TryOrderClosedDag(
            baselineEvents,
            ImmutableArray<string>.Empty,
            out var orderedBaseline);
        var baselineIdentityPrefix = orderedBaseline.Select(static item => item.Identity).ToImmutableArray();
        _ = DagLedgerLoader.TryOrderClosedDag(currentEvents, baselineIdentityPrefix, out var orderedCurrent);
        return ValidateLoaded(
            current,
            baseline,
            lean,
            baselineLean,
            dag,
            baselineDag,
            repository,
            frozenEvidenceRepository,
            ToSyntax(orderedBaseline),
            ToSyntax(orderedCurrent));
    }

    private static AdmissionOutcome? ValidateLoaded(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        AcceptedLeanClosure lean,
        AcceptedLeanClosure baselineLean,
        AcyclicTruthDag dag,
        AcyclicTruthDag baselineDag,
        IRepositoryGateway repository,
        IRepositoryGateway? frozenEvidenceRepository,
        FrozenLedgerSyntax baselineSyntax,
        FrozenLedgerSyntax currentSyntax)
    {
        var baselineReferences = FrozenLedger.ScanReferences(baselineSyntax);
        var currentReferences = FrozenLedger.ScanReferences(currentSyntax);
        if (baselineReferences is FrozenLedgerReferenceScanOutcome.Rejected invalidBaselineReferences)
        {
            return Reject("protected baseline ledger fields are invalid: " + invalidBaselineReferences.Message);
        }

        if (currentReferences is FrozenLedgerReferenceScanOutcome.Rejected invalidCurrentReferences)
        {
            return Reject("candidate ledger fields are invalid: " + invalidCurrentReferences.Message);
        }


        TrustedFrozenGitReferences trustedBaselineReferences;
        TrustedFrozenGitReferences trustedCurrentReferences;
        try
        {
            var evidenceRepositories = frozenEvidenceRepository is null
                ? new[] { repository }
                : new[] { frozenEvidenceRepository, repository };
            trustedBaselineReferences = FrozenEvidenceResolver.Validate(
                ((FrozenLedgerReferenceScanOutcome.Accepted)baselineReferences).References,
                evidenceRepositories);
            trustedCurrentReferences = FrozenEvidenceResolver.Validate(
                ((FrozenLedgerReferenceScanOutcome.Accepted)currentReferences).References,
                evidenceRepositories);
        }
        catch (InvalidOperationException exception)
        {
            return Reject("frozen ledger Git references are invalid: " + exception.Message);
        }

        var baselineMaterials = FrozenLedgerMaterializer.Build(
            baseline,
            baselineLean,
            baselineDag,
            baselineSyntax);
        if (baselineMaterials is FrozenMaterialOutcome.Rejected baselineMaterialFailure)
        {
            return Reject("protected baseline ledger material is invalid: " + baselineMaterialFailure.Message);
        }

        var validatedBaseline = FrozenLedger.ValidateHistory(
            baselineSyntax,
            ((FrozenMaterialOutcome.Accepted)baselineMaterials).Capability,
            trustedBaselineReferences);
        if (validatedBaseline is FrozenLedgerValidationOutcome.Rejected baselineFailure)
        {
            return Reject("protected baseline ledger is invalid: " + baselineFailure.Message);
        }

        var baselineCapability = ((FrozenLedgerValidationOutcome.Accepted)validatedBaseline).Capability;
        var receiptStore = TrustedRevocationReceiptStore.Materialize(
            baselineCapability,
            baseline,
            ((FrozenLedgerReferenceScanOutcome.Accepted)currentReferences)
                .References.RevocationReceiptBlobOids);
        if (receiptStore is RevocationReceiptStoreOutcome.Rejected receiptFailure)
        {
            return Reject("candidate revocation receipt material is invalid: " + receiptFailure.Message);
        }

        var currentMaterials = FrozenLedgerMaterializer.Build(current, lean, dag, currentSyntax);
        if (currentMaterials is FrozenMaterialOutcome.Rejected currentMaterialFailure)
        {
            return Reject("candidate ledger material is invalid: " + currentMaterialFailure.Message);
        }

        var validatedCandidate = FrozenLedger.ValidateCandidate(
            currentSyntax,
            baselineCapability,
            ((FrozenMaterialOutcome.Accepted)currentMaterials).Capability,
            trustedCurrentReferences,
            ((RevocationReceiptStoreOutcome.Accepted)receiptStore).Capability);
        return validatedCandidate is FrozenLedgerValidationOutcome.Rejected candidateFailure
            ? Reject("candidate ledger is invalid: " + candidateFailure.Message)
            : null;
    }

    private static bool RetainsBaselineFilesByteForByte(
        ImmutableArray<RepositoryFile> baselineFiles,
        RepositorySnapshot current) =>
        baselineFiles.All(baselineFile =>
            current.TryGetFile(baselineFile.Path.Value, out var currentFile)
            && currentFile!.RawBytes.AsSpan().SequenceEqual(baselineFile.RawBytes.AsSpan()));

    private static FrozenLedgerSyntax ToSyntax(ImmutableArray<DagLedgerFileEvent> events)
    {
        var raw = ImmutableArray.CreateBuilder<byte>();
        var lines = ImmutableArray.CreateBuilder<FrozenLedgerLineSyntax>();
        var previous = FrozenLedgerCanonicalWriter.ZeroHash;
        var dagToLinearHash = new Dictionary<string, string>(StringComparer.Ordinal);
        for (var sequence = 0; sequence < events.Length; sequence++)
        {
            var item = events[sequence];
            var payload = item.Payload;
            if (payload.TryGetProperty("previous_attestation_event_hash", out var dagPrevious))
            {
                var rewritten = JsonNode.Parse(payload.GetRawText())!.AsObject();
                rewritten["previous_attestation_event_hash"] = dagToLinearHash[dagPrevious.GetString()!];
                payload = JsonSerializer.SerializeToElement(rewritten);
            }

            var encoded = FrozenLedgerCanonicalWriter.WriteEvent(
                item.EventType,
                payload,
                previous,
                sequence);
            using var document = JsonDocument.Parse(encoded.Bytes.AsSpan()[..^1].ToArray());
            var line = new FrozenLedgerLineSyntax(encoded.Bytes, document.RootElement.Clone());
            raw.AddRange(encoded.Bytes);
            lines.Add(line);
            dagToLinearHash.Add(item.EventHash, encoded.Hash);
            previous = encoded.Hash;
        }

        return new FrozenLedgerSyntax(raw.ToImmutable(), lines.ToImmutable());
    }

    private static AdmissionOutcome? ValidateTransition(
        RepositorySnapshot baseline,
        AcceptedLeanClosure baselineLean,
        AcyclicTruthDag baselineDag,
        IRepositoryGateway repository,
        IRepositoryGateway? frozenEvidenceRepository,
        RepositoryFile baselineFile,
        ImmutableArray<RepositoryFile> currentFiles)
    {
        var baselineLoad = DagLedgerLoader.Load(baselineFile.RawBytes.AsSpan());
        if (baselineLoad is DagLedgerLoadOutcome.Invalid invalidBaseline)
        {
            return Reject("protected baseline ledger syntax is invalid: " + invalidBaseline.Message);
        }

        var baselineSyntax = ((DagLedgerLoadOutcome.Loaded)baselineLoad).Syntax;
        var baselineReferences = FrozenLedger.ScanReferences(baselineSyntax);
        if (baselineReferences is FrozenLedgerReferenceScanOutcome.Rejected invalidBaselineReferences)
        {
            return Reject("protected baseline ledger fields are invalid: " + invalidBaselineReferences.Message);
        }

        TrustedFrozenGitReferences trustedBaselineReferences;
        try
        {
            var evidenceRepositories = frozenEvidenceRepository is null
                ? new[] { repository }
                : new[] { frozenEvidenceRepository, repository };
            trustedBaselineReferences = FrozenEvidenceResolver.Validate(
                ((FrozenLedgerReferenceScanOutcome.Accepted)baselineReferences).References,
                evidenceRepositories);
        }
        catch (InvalidOperationException exception)
        {
            return Reject("frozen ledger Git references are invalid: " + exception.Message);
        }

        var baselineMaterials = FrozenLedgerMaterializer.Build(
            baseline,
            baselineLean,
            baselineDag,
            baselineSyntax);
        if (baselineMaterials is FrozenMaterialOutcome.Rejected baselineMaterialFailure)
        {
            return Reject("protected baseline ledger material is invalid: " + baselineMaterialFailure.Message);
        }

        var validatedBaseline = FrozenLedger.ValidateHistory(
            baselineSyntax,
            ((FrozenMaterialOutcome.Accepted)baselineMaterials).Capability,
            trustedBaselineReferences);
        if (validatedBaseline is FrozenLedgerValidationOutcome.Rejected baselineFailure)
        {
            return Reject("protected baseline ledger is invalid: " + baselineFailure.Message);
        }

        var filesLoad = DagLedgerLoader.LoadFiles(currentFiles);
        if (filesLoad is DagLedgerFilesLoadOutcome.Invalid invalidFiles)
        {
            return Reject("candidate content-addressed ledger is invalid: " + invalidFiles.Message);
        }

        var candidates = ((DagLedgerFilesLoadOutcome.Loaded)filesLoad).Events;
        if (!TryProveBijection(
            baselineSyntax,
            candidates,
            ignoreDagDependencies: true,
            out var migrationFailure))
        {
            return Reject("candidate content-addressed ledger migration is invalid: " + migrationFailure);
        }

        var dagFailure = DagLedgerLoader.ValidateClosedDag(candidates);
        if (dagFailure is not null)
        {
            return Reject("candidate content-addressed ledger is invalid: " + dagFailure);
        }

        if (!TryProveBijection(
            baselineSyntax,
            candidates,
            ignoreDagDependencies: false,
            out migrationFailure))
        {
            return Reject("candidate content-addressed ledger migration is invalid: " + migrationFailure);
        }

        return null;
    }

    private static bool TryProveBijection(
        FrozenLedgerSyntax baseline,
        ImmutableArray<DagLedgerFileEvent> candidates,
        bool ignoreDagDependencies,
        out string message)
    {
        message = string.Empty;
        if (baseline.Lines.Length != candidates.Length)
        {
            message = "legacy events and content-addressed files are not a bijection.";
            return false;
        }

        var unused = candidates.ToList();
        var hashMap = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var line in baseline.Lines)
        {
            var legacy = line.Value;
            var eventType = legacy.GetProperty("event_type").GetString()!;
            var payload = legacy.GetProperty("payload");
            var oldHash = legacy.GetProperty("event_hash").GetString()!;
            DagLedgerFileEvent? candidate;
            if (eventType == "Genesis")
            {
                var matches = unused.Where(static item => item.EventType == "Genesis").ToArray();
                candidate = matches.Length == 1 ? matches[0] : null;
            }
            else if (payload.TryGetProperty("frozen_node_id", out var frozenNodeId)
                && frozenNodeId.ValueKind == JsonValueKind.String)
            {
                candidate = unused.SingleOrDefault(item =>
                    string.Equals(item.Identity, frozenNodeId.GetString(), StringComparison.Ordinal));
            }
            else
            {
                var matches = unused.Where(item =>
                    item.EventType == eventType && PayloadEqual(payload, item.Payload, ignoreDagDependencies))
                    .ToArray();
                candidate = matches.Length == 1 ? matches[0] : null;
            }

            if (candidate is null
                || candidate.EventType != eventType)
            {
                message = "legacy events and content-addressed files are not a bijection.";
                return false;
            }

            if (!PayloadEqual(payload, candidate.Payload, ignoreDagDependencies))
            {
                message = "candidate payload differs from protected baseline.";
                return false;
            }

            if (payload.TryGetProperty("previous_attestation_event_hash", out var oldPrevious))
            {
                if (!hashMap.TryGetValue(oldPrevious.GetString()!, out var expectedPrevious)
                    || !candidate.Payload.TryGetProperty("previous_attestation_event_hash", out var newPrevious)
                    || !string.Equals(newPrevious.GetString(), expectedPrevious, StringComparison.Ordinal))
                {
                    message = "previous_attestation_event_hash does not preserve the old attestation hash mapping.";
                    return false;
                }
            }

            unused.Remove(candidate);
            hashMap.Add(oldHash, candidate.EventHash);
        }

        if (unused.Count != 0)
        {
            message = "legacy events and content-addressed files are not a bijection.";
            return false;
        }

        return true;
    }

    private static bool PayloadEqual(JsonElement left, JsonElement right, bool ignoreDagDependencies)
    {
        var leftFields = left.EnumerateObject()
            .Where(property => !IsTransitionDependency(property.Name, ignoreDagDependencies))
            .ToArray();
        var rightFields = right.EnumerateObject()
            .Where(property => !IsTransitionDependency(property.Name, ignoreDagDependencies))
            .ToArray();
        return leftFields.Length == rightFields.Length
            && leftFields.Zip(rightFields).All(pair =>
                pair.First.NameEquals(pair.Second.Name)
                && string.Equals(pair.First.Value.GetRawText(), pair.Second.Value.GetRawText(), StringComparison.Ordinal));
    }

    private static bool IsTransitionDependency(string field, bool ignoreDagDependencies) =>
        field == "previous_attestation_event_hash"
        || (ignoreDagDependencies && field == "prerequisite_frozen_node_ids");

    private static ImmutableArray<RepositoryFile> AcceptedFiles(RepositorySnapshot snapshot) =>
        snapshot.Files.Values
            .Where(static file => FrozenLedgerChangeClassifier.IsAcceptedEventPath(file.Path.Value))
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .ToImmutableArray();

    private static bool HasInvalidAcceptedFiles(RepositorySnapshot snapshot) =>
        snapshot.Files.Keys.Any(static path =>
            path.Value.StartsWith(FrozenLedgerChangeClassifier.AcceptedRoot + "/", StringComparison.Ordinal)
            && !FrozenLedgerChangeClassifier.IsAcceptedEventPath(path.Value));

    private static AdmissionOutcome Reject(string message)
    {
        var descriptor = RuleCatalog.Default.Descriptors[7];
        return new AdmissionOutcome.RuleRejected(ImmutableArray.Create(new Diagnostic(
            descriptor.Id,
            descriptor.Title,
            descriptor.DisplaySeverity,
            descriptor.AdmissionEffect,
            FrozenLedgerChangeClassifier.LedgerPath,
            message)));
    }
}
