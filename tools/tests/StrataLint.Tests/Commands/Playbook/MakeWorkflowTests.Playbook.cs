namespace StrataLint.Tests;

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

        foreach (var target in new[] { "deliver-check", "receipts-stage" })
        {
            Assert.Contains($"make {target}", makefile, StringComparison.Ordinal);
            Assert.Contains(
                $"scripts/workflow/playbook-workflows.sh {target} \"$(BASE)\"",
                makefile,
                StringComparison.Ordinal);
        }

        foreach (var target in new[] { "deposit", "cover" })
        {
            Assert.Contains($"make {target} ATOM_ID=", makefile, StringComparison.Ordinal);
            Assert.Contains(
                $"scripts/workflow/playbook-workflows.sh {target} \"$(BASE)\" \"$(ATOM_ID)\" \"$(GID)\"",
                makefile,
                StringComparison.Ordinal);
        }

        Assert.Contains("make cover-batch ATOMS=", makefile, StringComparison.Ordinal);
        Assert.Contains(
            "scripts/workflow/playbook-workflows.sh cover-batch \"$(BASE)\" \"$(ATOMS)\"",
            makefile,
            StringComparison.Ordinal);

        Assert.Contains("ledger-append --candidate-lean-report", script, StringComparison.Ordinal);
        Assert.Contains("digest-status --base", script, StringComparison.Ordinal);
        Assert.Contains("run_cli freeze-status --path \"$MODULE_PATH\"", script, StringComparison.Ordinal);
        Assert.DoesNotContain("replay_reattests", script, StringComparison.Ordinal);
        Assert.DoesNotContain("jq -rsc", script, StringComparison.Ordinal);
    }
}
