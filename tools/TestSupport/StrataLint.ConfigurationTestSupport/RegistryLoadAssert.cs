using StrataLint.Engine;

namespace StrataLint.TestSupport;

/// Asserting the outcome type alone reports which case was returned but not why. A
/// registry that fails to load carries its reason in InfrastructureFailure.Message --
/// for example the exact canonical-order violation in domains.yaml -- and a bare
/// Assert.IsType discards it, leaving a reader with "expected Accepted, got
/// InfrastructureFailure" and no path to the cause except reading RegistryPolicy.
/// See #993: the judgement is right, the reported material is not the one judged.
public static class RegistryLoadAssert
{
    public static RegistryLoadOutcome.Accepted Accepted(RegistryLoadOutcome outcome) =>
        outcome as RegistryLoadOutcome.Accepted
        ?? throw new Xunit.Sdk.XunitException(
            outcome is RegistryLoadOutcome.InfrastructureFailure failure
                ? $"registry load failed: {failure.Message}"
                : $"registry load returned {outcome.GetType().Name}, expected Accepted");
}
