using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void BranchesRemainOutsideCleanupInBothModes(bool force, bool lanesOnly)
    {
        using var fixture = new CleanLanesFixture();
        string[] branches =
        [
            "lane/governance/unattached-merged", "harness/unattached-merged",
            "lane/governance/recovery-existing", "feature/unattached-merged",
        ];
        foreach (var branch in branches) fixture.AddOrphan(branch, merged: true);
        fixture.AddOrphan("harness/unattached-unmerged", merged: false);
        var judge = fixture.AddGitlessJudgeSnapshot("trureturing-judge-control");
        var before = CleanLanesFixture.Git(fixture.RepositoryRoot,
            "for-each-ref", "--format=%(refname) %(objectname)", "refs/heads");
        var runner = fixture.CreateRunner();
        var arguments = new List<string>();
        if (force) arguments.Add("--force");
        if (lanesOnly) arguments.Add("--lanes-only");

        var result = fixture.RunWithRaw(runner, arguments.ToArray());

        Assert.True(result.Success, result.Error);
        Assert.Equal(before, CleanLanesFixture.Git(fixture.RepositoryRoot,
            "for-each-ref", "--format=%(refname) %(objectname)", "refs/heads"));
        Assert.DoesNotContain(ReadItems(result.Output), item =>
            item.GetProperty("kind").GetString() == "orphan_branch"
            || item.GetProperty("path").ValueKind == System.Text.Json.JsonValueKind.Null
                && item.GetProperty("branch").ValueKind != System.Text.Json.JsonValueKind.Null);
        Assert.DoesNotContain(runner.Invocations, call => IsProtocol(call.Arguments, "retire-branch")
            || call.FileName == "git" && call.Arguments.Contains("update-ref") && call.Arguments.Contains("-d"));
        Assert.Equal(!force || lanesOnly, Directory.Exists(judge));
        Assert.Empty(ReadEvents(result.Error, "clean_lanes_warning"));
    }
}
