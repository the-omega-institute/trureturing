using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData("dirty")]
    [InlineData("staged")]
    [InlineData("index.lock")]
    [InlineData("held-index.lock")]
    [InlineData("MERGE_HEAD")]
    [InlineData("private")]
    public void ElapsedLockCheckpointsOrdinaryChangesAndReportsNativeFailures(string material)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/disposable-lock");
        fixture.LockLane(lane);
        if (material is "dirty" or "staged")
        {
            File.WriteAllText(Path.Combine(lane, "README.md"), "unpublished bytes\n");
            if (material == "staged") CleanLanesFixture.Git(lane, "add", "README.md");
        }
        else File.WriteAllText(Path.Combine(fixture.WorktreeGitDirectory(lane),
            material == "held-index.lock" ? "index.lock" : material), "local recovery\n");
        using var holder = material == "held-index.lock"
            ? File.Open(Path.Combine(fixture.WorktreeGitDirectory(lane), "index.lock"),
                FileMode.Open, FileAccess.ReadWrite, FileShare.ReadWrite) : null;
        var runner = fixture.CreateRunner((file, args, _) =>
        {
            if (args.Contains("active-paths")) throw new InvalidOperationException("activity inspection must not run");
            return null;
        });
        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");
        var failed = material is "MERGE_HEAD" or "held-index.lock";
        Assert.Equal(!failed, result.Success);
        Assert.Equal(failed, Directory.Exists(lane));
        Assert.True(fixture.BranchExists("harness/disposable-lock"));
        if (failed) Assert.StartsWith("checkpoint_failed:", ReasonFor(result.Output, lane));
        if (material is "index.lock" or "held-index.lock")
        {
            var receipt = Assert.Single(ReadItems(result.Output), item => item.GetProperty("path").GetString() == lane);
            var clearance = Assert.Single(receipt.GetProperty("native_locks").EnumerateArray());
            Assert.EndsWith("index.lock", clearance.GetProperty("path").GetString());
            Assert.True(clearance.GetProperty("size").GetInt64() > 0);
            Assert.True(clearance.GetProperty("age_seconds").GetDouble() >= 0);
            Assert.Equal(material == "held-index.lock" ? "held" : "native_lock_cleared",
                clearance.GetProperty("status").GetString());
        }
    }

    [Fact]
    public void SuppliedActivityCannotVetoAnElapsedLock()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/disposable-active");
        fixture.LockLane(lane);
        var result = fixture.RunWithActivePath(lane, "--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        Assert.True(fixture.BranchExists("harness/disposable-active"));
    }
}
