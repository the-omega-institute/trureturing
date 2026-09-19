using System.Text;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // Publication and packaging use this class's private compiler stage.
    [Theory]
    [InlineData("test_native.NativeTests.test_compiler_origin_imports_and_invalidation")]
    [InlineData("test_native.NativeTests.test_native_facet_supplies_toolchain_environment")]
    [InlineData("test_native.NativeTests.test_binding_driver_environment_survives_interpreter_shutdown")]
    [InlineData("test_native.NativeTests.test_mapped_image_matches_loaded_bytes")]
    [InlineData("test_streaming")]
    [InlineData("test_reuse")]
    [InlineData("test_native.NativeTests.test_report_entry_reuses_complete_receipt_and_rechecks_current_inputs")]
    [InlineData("test_native_support.GuardedCommandTests")]
    [InlineData("test_native.NativeTests.test_coordinates_use_private_temporary_memo_and_clean_up_failures")]
    [InlineData("test_native.NativeTests.test_coordinates_reuse_warm_tree_memo")]
    [InlineData("test_native.NativeTests.test_input_verification_is_read_only")]
    [InlineData("test_native.NativeTests.test_publication_validates_material_identities_once")]
    [InlineData("test_native.NativeTests.test_aggregation_validates_each_row_once_and_preserves_rejection_statuses")]
    [InlineData("test_native.NativeTests.test_native_publication_rejects_incoming_damage_before_normalization")]
    [InlineData("test_native.NativeTests.test_publication_snapshot_integrity_and_replace_failure")]
    [InlineData("test_native.NativeTests.test_native_producer_inputs")]
    [InlineData("test_native.NativeTests.test_native_compiler_seed_is_private")]
    [InlineData("test_native.NativeTests.test_native_semantic_version_and_config")]
    [InlineData("test_native.NativeTests.test_native_invalid_semantic_versions")]
    [InlineData("test_native.NativeTests.test_native_pack_unpack_reuses_complete_rows")]
    [InlineData("test_native.NativeTests.test_native_clonefile_seed_reuses_rows_and_keeps_donor_private")]
    [InlineData("test_native.NativeTests.test_snapshot_generation_preserves_mathlib_partition")]
    [InlineData("test_native.NativeTests.test_release_publisher_legacy_seed_current_pack_restore_and_unchanged")]
    [InlineData("test_native.NativeTests.test_release_partition_preserves_semantic_and_selection_changes")]
    public void InspectorArtifactBehavior(string suite) => InspectorNativeTestRunner.Run(compiler, suite);
}

internal static class InspectorNativeTestRunner
{
    internal static void Run(InspectorCompilerFixture compiler, string suite)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        string[] environment = suite.StartsWith("test_native.", StringComparison.Ordinal)
            ? [$"STRATALINT_NATIVE_COMPILER_SEED={compiler.Path}"] : [];
        var result = TestProcessRunner.Run("env",
            [.. environment, "python3", "-B", "-m", "unittest", suite, "-v"],
            Path.Combine(root, "tools/lean-inspector/tests"), TestBudgets.ReportSupervisorHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError));
    }
}

public sealed class InspectorCompilerFixture : IDisposable
{
    private readonly TemporaryDirectory temporary = new();
    private readonly Lazy<string> stage;

    public InspectorCompilerFixture()
    {
        stage = new Lazy<string>(() =>
        {
            var root = TestRepositoryLayout.FindRoot();
            var result = TestProcessRunner.Run("python3",
                ["-B", "test_native_support.py", temporary.Path],
                System.IO.Path.Combine(root, "tools/lean-inspector/tests"),
                TestBudgets.ReportSupervisorHangGuard, 1024 * 1024);
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
                + Encoding.UTF8.GetString(result.StandardError));
            return temporary.Path;
        });
    }

    public string Path => stage.Value;

    public void Dispose() => temporary.Dispose();
}
