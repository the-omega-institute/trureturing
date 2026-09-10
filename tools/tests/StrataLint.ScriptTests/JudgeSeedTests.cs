using System.Text;

namespace StrataLint.Tests;

public sealed class JudgeSeedTests
{
    [Theory]
    [InlineData("test_checkout_and_runtime_copy")]
    [InlineData("test_helper_readme_commit_and_source_change")]
    [InlineData("test_semantics_membership_and_clean_equivalence")]
    [InlineData("test_corrupt_missing_material_and_relocation")]
    [InlineData("test_no_seed_or_save_failure_cannot_pass_bad_compilation")]
    public void CompiledSeedsFollowTheRealCompiler(string behavior)
    {
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            [Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/judge_seed_contract.py"), "CompilerSeeds." + behavior],
            root, TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
