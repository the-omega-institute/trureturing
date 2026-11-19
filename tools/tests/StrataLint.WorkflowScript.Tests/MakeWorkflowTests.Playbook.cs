namespace StrataLint.WorkflowScript.Tests;

public sealed partial class MakeWorkflowTests
{
    private const string PlaybookWorkflowScriptPath =
        "tools/scripts/workflow/playbook-workflows.sh";

    [Fact]
    public void PlaybookTargetsAreHelpedAndDelegateToOneCanonicalScript()
    {
        var root = TestRepositoryLayout.FindRoot();
        var makefile = File.ReadAllText(Path.Combine(root, "Makefile"));
        var script = File.ReadAllText(Path.Combine(root, PlaybookWorkflowScriptPath));

        foreach (var target in new[] { "deposit", "deposit-uncovered" })
            Assert.Equal($"\t@/bin/bash {PlaybookWorkflowScriptPath} {target} \"$(BASE)\" \"$(GID)\"", Recipe(makefile, target));

        Assert.Contains(
            "ledger-align --add \"$MODULE_PATH\" --candidate-lean-report \"$REPORT\"",
            script,
            StringComparison.Ordinal);
        Assert.Contains(
            "run_cli \"${align_args[@]}\" --candidate-lean-report .lake/build/stratalint/scoped-lean-report.json",
            script,
            StringComparison.Ordinal);
        Assert.DoesNotContain("run_cli ledger-align --candidate-lean-report \"$REPORT\"", script, StringComparison.Ordinal);
    }
}
