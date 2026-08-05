namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    private const string PlaybookWorkflowScriptPath =
        "Meta/StrataLint/scripts/playbook-workflows.sh";

    [Fact]
    public void PlaybookTargetsAreHelpedAndDelegateToOneCanonicalScript()
    {
        var root = FindRepositoryRoot();
        var makefile = File.ReadAllText(Path.Combine(root, "Makefile"));
        var script = File.ReadAllText(Path.Combine(root, PlaybookWorkflowScriptPath));

        foreach (var target in new[] { "deliver-check", "receipts-stage", "derived-refresh" })
        {
            Assert.Contains($"make {target}", makefile, StringComparison.Ordinal);
            Assert.Contains(
                $"playbook-workflows.sh {target} \"$(BASE)\"",
                makefile,
                StringComparison.Ordinal);
        }

        Assert.Contains("ledger-append --candidate-lean-report", script, StringComparison.Ordinal);
        Assert.Contains("digest-status --base", script, StringComparison.Ordinal);
    }
}
