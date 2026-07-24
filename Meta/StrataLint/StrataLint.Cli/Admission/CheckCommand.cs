using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record CheckArguments(
    string? ProtectedBase,
    string? CandidateLeanReport,
    string? BaselineLeanReport);

internal static class CheckCommand
{
    internal static AdmissionOutcome Run(
        IRepositoryGateway repository,
        IScribeEmissionVerifier? scribeEmissionVerifier,
        IReadOnlyList<string> arguments)
    {
        try
        {
            var options = ParseArguments(arguments);
            var prepared = repository.Prepare(options.ProtectedBase);
            var bootstrap = BootstrapGate.Evaluate(prepared.Changes);
            if (bootstrap is BootstrapOutcome.InfrastructureFailure bootstrapFailure)
            {
                return new AdmissionOutcome.InfrastructureFailure(bootstrapFailure.Message);
            }

            if (options.CandidateLeanReport is null || options.BaselineLeanReport is null)
            {
                return new AdmissionOutcome.InfrastructureFailure(
                    "check requires --candidate-lean-report FILE and --baseline-lean-report FILE");
            }

            var current = Decode(repository.ReadCurrent());
            var baseline = Decode(repository.ReadRevision(prepared.Revision));
            var candidateLeanReport = RawLeanReportArtifact.ReadFile(
                options.CandidateLeanReport,
                current);
            var verifiedScribeEmissions = VerifyScribeForAdmission(
                scribeEmissionVerifier,
                candidateLeanReport,
                bootstrap);
            var evaluation = SnapshotAdmissionCore.Evaluate(
                current,
                baseline,
                candidateLeanReport,
                RawLeanReportArtifact.ReadFile(options.BaselineLeanReport, baseline),
                prepared.Changes,
                bootstrap,
                verifiedScribeEmissions);
            var admission = evaluation.Outcome;
            if (admission is not AdmissionOutcome.Admitted
                && admission is not AdmissionOutcome.ProtectedSurfaceChange)
            {
                return admission;
            }

            if (evaluation is not
                {
                    CurrentLean: { } lean,
                    BaselineLean: { } baselineLean,
                    CurrentDag: { } dag,
                    BaselineDag: { } baselineDag,
                })
            {
                return new AdmissionOutcome.InfrastructureFailure(
                    "snapshot admission omitted capabilities required by frozen-ledger validation");
            }

            var ledgerOutcome = ProductionFrozenLedgerValidator.Validate(
                current,
                baseline,
                lean,
                baselineLean,
                dag,
                baselineDag,
                repository);
            var sl022Diagnostics = bootstrap is BootstrapOutcome.HumanReviewRequired review
                ? BootstrapGate.CreateSl022Diagnostics(review.ChangeSet)
                : ImmutableArray<Diagnostic>.Empty;
            return ledgerOutcome is null
                ? admission
                : SnapshotAdmissionCore.PreserveSl022Diagnostics(
                    ledgerOutcome,
                    sl022Diagnostics);
        }
        catch (Exception exception)
        {
            return new AdmissionOutcome.InfrastructureFailure(exception.Message);
        }
    }

    internal static VerifiedScribeEmissions? VerifyScribeForAdmission(
        IScribeEmissionVerifier? verifier,
        LeanAxiomReport report,
        BootstrapOutcome bootstrap)
    {
        if (verifier is null)
        {
            return null;
        }

        try
        {
            return verifier.Verify(report);
        }
        catch (InvalidOperationException) when (
            bootstrap is BootstrapOutcome.HumanReviewRequired)
        {
            return null;
        }
    }

    private static CheckArguments ParseArguments(IReadOnlyList<string> arguments)
    {
        string? protectedBase = null;
        string? candidateLeanReport = null;
        string? baselineLeanReport = null;
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count)
            {
                throw Usage();
            }

            var target = arguments[index] switch
            {
                "--protected-base" or "--merge-base" when protectedBase is null => 0,
                "--candidate-lean-report" when candidateLeanReport is null => 1,
                "--baseline-lean-report" when baselineLeanReport is null => 2,
                _ => throw Usage(),
            };
            switch (target)
            {
                case 0:
                    protectedBase = arguments[index + 1];
                    break;
                case 1:
                    candidateLeanReport = arguments[index + 1];
                    break;
                case 2:
                    baselineLeanReport = arguments[index + 1];
                    break;
            }
        }

        return new CheckArguments(protectedBase, candidateLeanReport, baselineLeanReport);
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint check [--protected-base REV] "
        + "--candidate-lean-report FILE --baseline-lean-report FILE");

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
}
