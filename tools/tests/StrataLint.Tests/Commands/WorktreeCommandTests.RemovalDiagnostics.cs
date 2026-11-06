namespace StrataLint.Tests;

public sealed partial class WorktreeCommandTests
{
    public static IEnumerable<object[]> NativeRemovalDiagnosticCases()
    {
        foreach (var consumer in new[] { "pool", "idle_cleanup", "remove", "explicit", "expired_cleanup" })
        foreach (var outcome in new[] { "qualification_failed", "checkpoint_failed", "partial_or_indeterminate" })
            yield return [consumer, outcome];
        foreach (var consumer in new[] { "pool", "idle_cleanup" })
        foreach (var outcome in new[] { "refused", "revalidate", "inspect_refused", "inspect" })
            yield return [consumer, outcome];
        foreach (var consumer in new[] { "remove", "explicit", "expired_cleanup" })
            yield return [consumer, "refused"];
        yield return ["pool", "inventory"];
        yield return ["pool", "pressure"];
        foreach (var consumer in new[] { "pool", "remove", "explicit" })
            yield return [consumer, "multiple"];
    }

    [Theory]
    [MemberData(nameof(NativeRemovalDiagnosticCases))]
    public void NativeRemovalConsumersPreserveBoundedFailures(string consumer, string outcome)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3", ["-B",
            Path.Combine(root, "tools/tests/StrataLint.WorkflowScript.Tests/Fixtures/native_removal_diagnostics.py"),
            root, consumer, outcome], root, TestBudgets.ProtocolProbeHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, System.Text.Encoding.UTF8.GetString(result.StandardOutput)
            + System.Text.Encoding.UTF8.GetString(result.StandardError));
    }
}
