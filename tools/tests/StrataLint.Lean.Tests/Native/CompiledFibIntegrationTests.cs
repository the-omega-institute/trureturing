using System.Text;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

public sealed class CompiledFibIntegrationTests
{
    [Theory]
    [InlineData("test_positive_source_native_macro_and_boundaries")]
    [InlineData("test_noop_and_unrelated_preserve_artifact_and_leaves")]
    [InlineData("test_private_transitive_source_and_layer_dependency_updates")]
    [InlineData("test_membership_removal_addition_and_eligibility")]
    [InlineData("test_invalid_native_bridge_fails_compilation")]
    [InlineData("test_native_reader_and_target_dependency_updates")]
    public void CompilerArtifactConsumer(string behavior)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        string[] sources = ["Reg/Support/AuricFibCompiledSource.lean",
            "Reg/Support/AuricFibCompiledFixture.lean"];
        var ownsSources = sources.All(path => !File.Exists(Path.Combine(root, path)));
        try
        {
            var result = TestProcessRunner.Run("python3",
                ["-B", "tools/lean-inspector/tests/test_auric_fib_compiled.py",
                    "CompiledFibIntegration." + behavior, "-v"], root,
                TestBudgets.ReportSupervisorHangGuard, 1024 * 1024);
            Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
                + Encoding.UTF8.GetString(result.StandardError));
        }
        finally
        {
            // The ordinary supervisor kills the complete child tree on its
            // unchanged guard; remove only sources this invocation could own.
            if (ownsSources)
                foreach (var path in sources) File.Delete(Path.Combine(root, path));
        }
    }
}
