namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    [Fact]
    public void PrShepherdWakesArmedPrsWhoseHeadHasNoChecks()
    {
        var root = FindRepositoryRoot();
        var shepherd = string.Join(
            '\n',
            File.ReadAllText(Path.Combine(root, PrShepherdScriptPath)),
            File.ReadAllText(Path.Combine(root, PrShepherdLeaseScriptPath)));

        // The sweep needs both head identity and check count to recognize an armed PR
        // whose token-authenticated push did not trigger a workflow.
        Assert.Contains("statusCheckRollup", shepherd, StringComparison.Ordinal);
        Assert.Contains("headRefOid", shepherd, StringComparison.Ordinal);

        // Observe the same checkless head twice so delayed check attachment is harmless.
        Assert.Contains("nochecks-", shepherd, StringComparison.Ordinal);

        var wakeIndex = shepherd.IndexOf("wake_pr()", StringComparison.Ordinal);
        Assert.True(wakeIndex >= 0, "the shepherd must define a wake action for checkless armed PRs");
        var wake = shepherd[wakeIndex..];
        var closeIndex = wake.IndexOf("pr close", StringComparison.Ordinal);
        var reopenIndex = wake.IndexOf("pr reopen", StringComparison.Ordinal);
        var rearmIndex = wake.IndexOf("--auto --merge", StringComparison.Ordinal);
        Assert.True(closeIndex >= 0, "wake must close the PR to mint a fresh trigger event");
        Assert.True(reopenIndex > closeIndex, "wake must reopen after close");
        Assert.True(rearmIndex > reopenIndex, "close disarms auto-merge; wake must re-arm it");
    }
}
