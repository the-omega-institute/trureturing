using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.TransportIntegration.Tests;

public sealed class ReportSnapshotTests
{
    [Theory]
    [InlineData("test_matching_report_donor_wins_over_later_incompatible_write")]
    [InlineData("test_report_preference_tracks_capture_inputs_only")]
    [InlineData("test_publication_keys_bind_actual_sealed_report_without_rehash_or_recapture")]
    [InlineData("test_missing_or_malformed_report_preserves_broad_check_seed_saving")]
    [InlineData("test_preferred_and_legacy_keys_keep_partition_integrity_and_writer_boundaries")]
    public void ReportCacheDonorsAndPublicationKeys(string behavior)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = EngineeringProcess.Process(root, "python3",
            ["-B", Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/report_snapshot_contract.py"),
                "SnapshotContracts." + behavior], hangGuard: TestBudgets.WorkflowProcessHangGuard, maximumOutputBytes: 1024 * 1024);
        Assert.True(result.Exit == 0, result.Text);
    }
}
