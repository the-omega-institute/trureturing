using System.Text;

namespace StrataLint.Tests;

public sealed class LeanCacheInputScriptTests
{
    [Fact]
    public void TruthReleaseConsumesOnlySelectedValidatedPushBundles()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            [Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/truth_release_contract.py")],
            root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void ImmutableResolutionAndOptionalActionsSeeds()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            [Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/ci_contract.py"),
                "Contracts", "LegacyCallerTests"],
            root, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("test_internal_dependency_file_links_round_trip_as_private_material")]
    [InlineData("test_invalid_dependency_links_disable_only_that_save_with_an_offending_path")]
    [InlineData("test_corrupt_dependency_seed_falls_back_without_replacing_current_material")]
    [InlineData("test_snapshot_readiness_and_material_follow_writer_permissions")]
    [InlineData("test_report_snapshot_keeps_only_current_complete_seed")]
    [InlineData("test_report_snapshot_rejects_invalid_current_without_using_history")]
    [InlineData("test_report_staging_and_restore_validate_independently")]
    [InlineData("test_report_export_requires_matching_handoff")]
    [InlineData("test_report_export_does_not_revalidate")]
    public void SnapshotReadinessAndMaterialRespectWriterPermissions(string behavior)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            [Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/ci_contract.py"), "SnapshotContracts." + behavior],
            root, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void ResolvedPartitionAndSemanticConfigurationBehavior()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            [Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/lean_input_contract.py"), "PartitionTests"],
            root, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
