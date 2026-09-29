using StrataLint.Engine;

namespace StrataLint.TestSupport;

/// Asserting the outcome type alone reports which case was returned but not why. A
/// repository policy that fails to load carries its reason in InfrastructureFailure.Message --
/// for example the exact canonical-order violation in domains.yaml -- and a bare
/// Assert.IsType discards it, leaving a reader with "expected Accepted, got
/// InfrastructureFailure" and no path to the cause except reading RepositoryPolicy.
/// See #993: the judgement is right, the reported material is not the one judged.
public static class PolicyLoadAssert
{
    public static PolicyLoadOutcome.Accepted Accepted(PolicyLoadOutcome outcome) =>
        outcome as PolicyLoadOutcome.Accepted
        ?? throw new Xunit.Sdk.XunitException(
            outcome is PolicyLoadOutcome.InfrastructureFailure failure
                ? $"repository policy load failed: {failure.Message}"
                : $"repository policy load returned {outcome.GetType().Name}, expected Accepted");
}
