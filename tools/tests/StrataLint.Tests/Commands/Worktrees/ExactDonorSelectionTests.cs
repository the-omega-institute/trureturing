using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class LeanCacheEnsureCommandTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ExactDonorChoosesLaterRegisteredWorktreeOverEligibleMainAndSibling(bool exact)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "main cache\n", projectWarm: true);
        var earlier = AddWorktree(repository.Path, "a-earlier");
        WriteCache(earlier, "earlier cache\n", projectWarm: true);
        var later = AddWorktree(repository.Path, "b-later");
        WriteCache(later, "later cache\n", projectWarm: true);
        var target = AddWorktree(repository.Path, "target");
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner();
        var arguments = new List<string> { "ensure-cache", "--path", target,
            "--donor-repository", repository.Path };
        if (exact) arguments.AddRange(["--donor-worktree", LeanCacheGuard.PhysicalPath(later)]);

        var result = WorktreeCommand.Run(repository.Path, arguments, runner, cloner);

        Assert.True(result.Success, result.Error);
        var expected = LeanCacheGuard.PhysicalPath(exact ? later : repository.Path);
        Assert.Equal(Path.Combine(expected, ".lake"), Assert.Single(cloner.Invocations).Source);
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal(expected, receipt.RootElement.GetProperty("donor").GetString());
        Assert.Equal(exact ? "later cache\n" : "main cache\n", LeanCacheFixtureFile.ReadCacheText(target));
        AssertNoCacheGet(runner);
        Assert.Equal(0, runner.ArchiveInvocations);
    }

    [Theory]
    [InlineData("mismatch")]
    [InlineData("busy-lock")]
    [InlineData("busy-process")]
    [InlineData("unregistered")]
    [InlineData("self")]
    [InlineData("symlink")]
    [InlineData("cache-symlink")]
    [InlineData("cold")]
    [InlineData("existing-target")]
    public void ExactDonorRejectionNeverFallsBackToEligibleMain(string scenario)
    {
        using var repository = new TemporaryDirectory();
        using var outside = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "main cache\n", projectWarm: true);
        var donor = AddWorktree(repository.Path, "requested-donor");
        WriteCache(donor, "donor cache\n", projectWarm: scenario != "cold");
        var target = AddWorktree(repository.Path, "target");
        var requested = LeanCacheGuard.PhysicalPath(donor);
        if (scenario == "mismatch") ChangeMathlibPartition(donor);
        if (scenario == "unregistered")
        {
            InitializeRepository(outside.Path);
            WriteCache(outside.Path, "unregistered cache\n", projectWarm: true);
            requested = LeanCacheGuard.PhysicalPath(outside.Path);
        }
        if (scenario == "self") requested = LeanCacheGuard.PhysicalPath(target);
        if (scenario == "symlink")
        {
            requested = Path.Combine(LeanCacheGuard.PhysicalPath(outside.Path), "alias");
            Directory.CreateSymbolicLink(requested, donor);
        }
        if (scenario == "cache-symlink")
        {
            Directory.Delete(Path.Combine(donor, ".lake"), recursive: true);
            Directory.CreateSymbolicLink(Path.Combine(donor, ".lake"), Path.Combine(repository.Path, ".lake"));
        }
        if (scenario == "existing-target") WriteCache(target, "retained target\n", projectWarm: true);
        using var busy = scenario == "busy-lock"
            ? LeanCacheGuard.TryAcquireExclusive(Path.Combine(donor, ".lake")) : null;
        if (scenario == "busy-lock") Assert.NotNull(busy);
        var runner = new RecordingWorktreeProcessRunner
        {
            BusyRoot = scenario == "busy-process" ? donor : null,
        };
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(repository.Path,
            ["ensure-cache", "--path", target, "--donor-worktree", requested], runner, cloner);

        Assert.False(result.Success);
        Assert.Empty(cloner.Invocations);
        AssertNoCacheGet(runner);
        Assert.Equal(0, runner.ArchiveInvocations);
        if (scenario == "existing-target")
            Assert.Equal("retained target\n", LeanCacheFixtureFile.ReadCacheText(target));
        else Assert.False(Directory.Exists(Path.Combine(target, ".lake")));
    }
}
