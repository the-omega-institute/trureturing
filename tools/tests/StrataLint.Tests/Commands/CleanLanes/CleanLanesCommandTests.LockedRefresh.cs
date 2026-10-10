using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void RefreshedLockIdentityIsProtected()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/lock-race");
        fixture.LockLane(lane);
        var reads = 0;
        var runner = fixture.CreateRunner((file, args, _) =>
        {
            if (file == "git" && args.SequenceEqual(new[] { "worktree", "list", "--porcelain", "-z" }) && ++reads == 2)
            {
                CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "worktree", "unlock", lane);
                fixture.LockLane(lane, "replacement");
            }
            return null;
        });
        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("locked_changed", ReasonFor(result.Output, lane));
    }
}
