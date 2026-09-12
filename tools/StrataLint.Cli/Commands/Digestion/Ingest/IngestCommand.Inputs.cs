using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    private static ValidatedPolicy LoadPolicy(RepositorySnapshot snapshot)
    {
        if (!snapshot.TryGetFile("Meta/FILEMAP.toml", out var fileMap)
            || !snapshot.TryGetFile("Meta/domains.yaml", out var domains))
        {
            throw new InvalidOperationException(
                "ingest requires Meta/FILEMAP.toml and Meta/domains.yaml");
        }

        return RepositoryPolicyLoader.Load(fileMap.RawBytes.AsSpan(), domains.RawBytes.AsSpan()) switch
        {
            PolicyLoadOutcome.Accepted accepted => accepted.Policy,
            PolicyLoadOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private static AcceptedLeanClosure ValidateLean(
        RepositorySnapshot snapshot,
        LeanAxiomReport report) =>
        LeanClosureValidator.Validate(snapshot, report) switch
        {
            LeanValidationOutcome.Accepted accepted => accepted.Capability,
            LeanValidationOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    internal static void RequireNoReceiptIntegrityFailure(
        DigestionLedgerEvaluation evaluation)
    {
        if (evaluation.HasReceiptIntegrityFailure)
        {
            throw new InvalidOperationException(
                "digest status is invalid: "
                + string.Join("; ", evaluation.ReceiptIntegrityFailureReasons));
        }
    }
}
