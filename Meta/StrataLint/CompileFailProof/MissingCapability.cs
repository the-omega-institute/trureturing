using StrataLint.Engine;

namespace StrataLint.CompileFailProof;

internal static class MissingCapability
{
    internal static AdmissionOutcome CannotForgeAdmission(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        ValidatedPolicy policy,
        AcceptedLeanClosure lean,
        AcceptedLeanClosure baselineLean,
        RawChangeSet changes) =>
        AdmissionPipeline.Evaluate(
            current,
            baseline,
            policy,
            lean,
            baselineLean,
            changes);
}
