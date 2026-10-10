using System.Text;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

public sealed class LeanReportScopedTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    [Theory]
    [InlineData("test_selected_utility_discovery_uses_production_reader")]
    [InlineData("test_rejects_empty_targets_and_canonical_destination")]
    [InlineData("test_scoped_bundle_checks_independent_membership_sources_and_materials")]
    [InlineData("test_scoped_inputs_exclude_siblings_and_program_bytes")]
    [InlineData("test_scoped_output_cannot_overlap_any_full_bundle_member")]
    [InlineData("test_scoped_output_preserves_full_seed_base")]
    public void ScopedProducerContract(string scenario) => Run(scenario, native: false);

    [Theory]
    [InlineData("test_native_selected_utility_reader_ignores_unrelated_unfinished_refutation")]
    [InlineData("test_native_scope_uses_only_explicit_module_facets")]
    [InlineData("test_native_scope_tracks_changed_imports_and_external_utility_claims")]
    [InlineData("test_native_scope_includes_external_consumer_and_checks_its_closure")]
    [InlineData("test_native_cached_scope_still_builds_program_and_clears_failure_seal")]
    public void ScopedProducerNativeContract(string scenario) => Run(scenario, native: true);

    private void Run(string scenario, bool native)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        string[] environment = native ? [$"STRATALINT_NATIVE_COMPILER_SEED={compiler.Path}"] : [];
        var result = TestProcessRunner.Run("env", [.. environment, "python3", "-B",
            Path.Combine(root, "tools/tests/StrataLint.Lean.Tests/Native/lean_report_scoped_fixture.py"), scenario],
            root, TestBudgets.ReportSupervisorHangGuard, 1024 * 1024);
        InspectorNativeTestRunner.WriteCommandObservations(result.StandardOutput);
        InspectorNativeTestRunner.WriteCommandObservations(result.StandardError);
        Assert.True(result.ExitCode == 0, "[FAIL] " + scenario + ": "
            + Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
