using StrataLint.Engine;

namespace StrataLint.TestSupport;

// 共享测试断言:原住在 StrataLint.Tests/Admission/ReviewRegressionTests.Helpers.cs ——
// 一个以某测试类命名的文件里。它被 StrataLint.Tests 的 14 个文件与
// StrataLint.ArchitectureTests 的 1 个共同消费,即**共享测试脚手架**,归宿是本程序集。
//
// 搬迁的意义在边上:ArchitectureTests → StrataLint.Tests 这条 test→test 边此前
// 混着两种理由 —— 「审计该程序集」(正当,见 BaseFactScopeProbeRatchetTests)与
// 「复用它的实现」(不正当)。剥掉后者,边只剩它该有的那个理由,
// 日后再混进复用会立刻可见。

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
