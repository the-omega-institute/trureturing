using System.Text;
using System.Text.Json;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

public sealed class InspectorNativeTests(InspectorCompilerFixture compiler) : IClassFixture<InspectorCompilerFixture>
{
    // Publication, coordinates and verification use this class's private compiler stage.
    [Theory]
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
    public void InspectorArtifactBehavior(string suite) => InspectorNativeTestRunner.Run(compiler, suite);
}

internal static class InspectorNativeTestRunner
{
    internal static void Run(InspectorCompilerFixture compiler, string suite)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var clock = TimeProvider.System;
        Console.WriteLine("NATIVE_CASE " + JsonSerializer.Serialize(new { phase = "start", suite, utc = clock.GetUtcNow() }));
        var prepared = clock.GetTimestamp();
        string[] environment = suite.StartsWith("test_native.", StringComparison.Ordinal)
            ? [$"STRATALINT_NATIVE_COMPILER_SEED={compiler.Path}"] : [];
        Console.WriteLine("NATIVE_CASE " + JsonSerializer.Serialize(new { phase = "compiler-ready", suite,
            utc = clock.GetUtcNow(), elapsed_ms = clock.GetElapsedTime(prepared).TotalMilliseconds }));
        var executed = clock.GetTimestamp();
        var result = TestProcessRunner.Run("env",
            [.. environment, "python3", "-B", "-m", "unittest", suite, "-v"],
            Path.Combine(root, "tools/lean-inspector/tests"), TestBudgets.ReportSupervisorHangGuard, 1024 * 1024);
        Console.WriteLine("NATIVE_CASE " + JsonSerializer.Serialize(new { phase = "child-exit", suite,
            utc = clock.GetUtcNow(), elapsed_ms = clock.GetElapsedTime(executed).TotalMilliseconds, raw_exit = result.ExitCode }));
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
