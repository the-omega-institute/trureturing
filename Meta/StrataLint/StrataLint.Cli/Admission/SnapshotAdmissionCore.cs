using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record SnapshotAdmissionEvaluation(
    AdmissionOutcome Outcome,
    AcceptedLeanClosure? CurrentLean,
    AcceptedLeanClosure? BaselineLean,
    AcyclicTruthDag? CurrentDag,
    AcyclicTruthDag? BaselineDag);

internal static class SnapshotAdmissionCore
{
    internal static SnapshotAdmissionEvaluation Evaluate(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        LeanAxiomReport currentReport,
        LeanAxiomReport baselineReport,
        RawChangeSet changes,
        BootstrapOutcome bootstrap,
        VerifiedScribeEmissions? verifiedScribeEmissions,
        RepositorySnapshot? forkPoint = null)
    {
        try
        {
            if (bootstrap is BootstrapOutcome.InfrastructureFailure bootstrapFailure)
            {
                return Failure(bootstrapFailure.Message);
            }

            var sl022Diagnostics = bootstrap is
                BootstrapOutcome.ProtectedSurfaceVerificationRequired bootstrapVerification
                ? BootstrapGate.CreateSl022Diagnostics(bootstrapVerification.ChangeSet)
                : ImmutableArray<Diagnostic>.Empty;
            if (!current.TryGetFile("Meta/registry.yaml", out var registryFile)
                || !current.TryGetFile("Meta/domains.yaml", out var domainsFile))
            {
                return Failure("current snapshot lacks Meta/registry.yaml or Meta/domains.yaml");
            }

            var registry = RegistryLoader.Load(
                registryFile.RawBytes.AsSpan(),
                domainsFile.RawBytes.AsSpan()) switch
            {
                RegistryLoadOutcome.Accepted accepted => accepted,
                RegistryLoadOutcome.InfrastructureFailure failure =>
                    throw new InvalidOperationException(failure.Message),
            };
            var lean = ValidateLean(current, currentReport);
            var baselineLean = ValidateLean(baseline, baselineReport);
            var dagOutcome = AcyclicTruthDag.Build(current, lean);
            if (dagOutcome is DagBuildOutcome.Rejected rejectedDag)
            {
                return new SnapshotAdmissionEvaluation(
                    RejectCycle(rejectedDag.Witness, sl022Diagnostics),
                    lean,
                    baselineLean,
                    null,
                    null);
            }

            var baselineDagOutcome = AcyclicTruthDag.Build(baseline, baselineLean);
            if (baselineDagOutcome is DagBuildOutcome.Rejected baselineRejected)
            {
                return Failure(
                    "protected baseline truth DAG is cyclic: "
                    + string.Join(" -> ", baselineRejected.Witness.Select(static path => path.Value)));
            }

            var admission = bootstrap switch
            {
                BootstrapOutcome.Clear clear => AdmissionPipeline.EvaluateWithScribe(
                    current,
                    baseline,
                    registry.Policy,
                    lean,
                    baselineLean,
                    changes,
                    clear.Capability,
                    verifiedScribeEmissions,
                    forkPoint),
                BootstrapOutcome.ProtectedSurfaceVerificationRequired protectedSurfaceVerification =>
                    AdmissionPipeline.EvaluateProtectedSurface(
                        current,
                        baseline,
                        registry.Policy,
                        lean,
                        baselineLean,
                        changes,
                        protectedSurfaceVerification.ChangeSet,
                        verifiedScribeEmissions,
                        forkPoint),
                _ => throw new InvalidOperationException("unknown bootstrap outcome"),
            };
            if (admission is not AdmissionOutcome.Admitted
                && admission is not AdmissionOutcome.ProtectedSurfaceChange)
            {
                admission = PreserveSl022Diagnostics(admission, sl022Diagnostics);
            }

            return new SnapshotAdmissionEvaluation(
                admission,
                lean,
                baselineLean,
                ((DagBuildOutcome.Accepted)dagOutcome).Capability,
                ((DagBuildOutcome.Accepted)baselineDagOutcome).Capability);
        }
        catch (Exception exception)
        {
            return Failure(exception.Message);
        }
    }

    private static SnapshotAdmissionEvaluation Failure(string message) => new(
        new AdmissionOutcome.InfrastructureFailure(message),
        null,
        null,
        null,
        null);

    private static AcceptedLeanClosure ValidateLean(
        RepositorySnapshot snapshot,
        LeanAxiomReport report) =>
        LeanClosureValidator.Validate(snapshot, report) switch
        {
            LeanValidationOutcome.Accepted accepted => accepted.Capability,
            LeanValidationOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private static AdmissionOutcome RejectCycle(
        ImmutableArray<RepoPath> witness,
        ImmutableArray<Diagnostic> sl022Diagnostics)
    {
        if (witness.Length < 2 || witness[0] != witness[^1])
        {
            throw new InvalidOperationException(
                "Truth DAG cycle rejection did not carry a closed witness.");
        }

        var descriptor = RuleCatalog.Default.Descriptors[0];
        var cycle = new Diagnostic(
            descriptor.Id,
            descriptor.Title,
            descriptor.DisplaySeverity,
            descriptor.AdmissionEffect,
            witness[0].Value,
            "managed import cycle: "
            + string.Join(" -> ", witness.Select(static path => path.Value)));
        return new AdmissionOutcome.RuleRejected(
            ImmutableArray.Create(cycle).AddRange(sl022Diagnostics));
    }

    internal static AdmissionOutcome PreserveSl022Diagnostics(
        AdmissionOutcome outcome,
        ImmutableArray<Diagnostic> expected)
    {
        if (expected.IsDefaultOrEmpty || outcome is not AdmissionOutcome.RuleRejected rejected)
        {
            return outcome;
        }

        var actual = rejected.Diagnostics
            .Where(static diagnostic => diagnostic.RuleId == RuleId.CreateKnown(22))
            .OrderBy(static diagnostic => diagnostic.Path, StringComparer.Ordinal)
            .ToImmutableArray();
        if (actual.IsEmpty)
        {
            return new AdmissionOutcome.RuleRejected(rejected.Diagnostics.AddRange(expected));
        }

        return actual.SequenceEqual(expected)
            ? outcome
            : new AdmissionOutcome.InfrastructureFailure(
                "SL-022 rejection evidence disagrees with the bootstrap meta change set");
    }
}
