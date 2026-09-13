using System.Text;

namespace StrataLint.Tests;

public sealed class InspectorNativeTests
{
    [Theory]
    [InlineData("test_streaming")]
    [InlineData("test_native.NativeTests.test_publication_validates_material_identities_once")]
    [InlineData("test_native.NativeTests.test_native_publication_rejects_incoming_damage_before_normalization")]
    [InlineData("test_native.NativeTests.test_publication_snapshot_integrity_and_replace_failure")]
    [InlineData("test_native.NativeTests.test_public_module_validates_and_private_job_is_not_a_target")]
    [InlineData("test_native.NativeTests.test_native_invalidation")]
    [InlineData("test_native.NativeTests.test_native_producer_inputs")]
    [InlineData("test_native.NativeTests.test_native_semantic_version_and_config")]
    [InlineData("test_native.NativeTests.test_native_invalid_semantic_versions")]
    [InlineData("test_native.NativeTests.test_native_recovery_and_required_failures")]
    [InlineData("test_native.NativeTests.test_native_recovers_only_row_with_damaged_deflate")]
    [InlineData("test_native.NativeTests.test_native_recovers_only_row_with_unsupported_compression")]
    [InlineData("test_native.NativeTests.test_native_pack_unpack_reuses_complete_rows")]
    [InlineData("test_native.NativeTests.test_snapshot_generation_preserves_lean_address")]
    public void InspectorArtifactBehavior(string suite)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", "-m", "unittest", suite, "-v"],
            Path.Combine(root, "tools/lean-inspector/tests"), TestBudgets.ReportSupervisorHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError));
    }
}
