using System.Collections.Immutable;
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
        var baselineFiles = baseline.Files.Values
            .Where(file => FrozenLedgerChangeClassifier.IsAcceptedEventPath(file.Path.Value))
            .OrderBy(file => file.Path.Value, StringComparer.Ordinal).ToArray();
        var currentFiles = current.Files.Values
            .Where(file => FrozenLedgerChangeClassifier.IsAcceptedEventPath(file.Path.Value))
            .OrderBy(file => file.Path.Value, StringComparer.Ordinal).ToArray();
        if (baselineFiles.Length == 0 || currentFiles.Length == 0)
        {
            return Reject("frozen ledger is missing from current or protected baseline");
        }

        if (!FrozenLedger.RetainsBaselineFilesByteForByte(
                baselineFiles.Select(file => (
                    file.Path.Value,
                    (ReadOnlyMemory<byte>)file.RawBytes.ToArray())),
                currentFiles.Select(file => (
                    file.Path.Value,
                    (ReadOnlyMemory<byte>)file.RawBytes.ToArray()))))
        {
            return Reject("candidate frozen ledger does not retain every baseline path byte-for-byte");
        }

        var baselineLoad = DagLedgerLoader.LoadFiles(baselineFiles.Select(file =>
            (file.Path.Value, (ReadOnlyMemory<byte>)file.RawBytes.ToArray())));
        var currentLoad = DagLedgerLoader.LoadFiles(currentFiles.Select(file =>
            (file.Path.Value, (ReadOnlyMemory<byte>)file.RawBytes.ToArray())));
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

    private static AdmissionOutcome Reject(string message)
    {
        var descriptor = RuleCatalog.Default.Descriptors[7];
        return new AdmissionOutcome.RuleRejected(ImmutableArray.Create(new Diagnostic(
            descriptor.Id,
            descriptor.Title,
            descriptor.DisplaySeverity,
            descriptor.AdmissionEffect,
            FrozenLedgerChangeClassifier.AcceptedRoot,
            message)));
    }
}
