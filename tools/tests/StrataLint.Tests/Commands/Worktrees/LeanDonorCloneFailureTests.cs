using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class LeanCacheEnsureCommandTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MainCheckoutMissingBuildCloneFailureCannotDownloadOrRunWriter(bool withWriter)
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var donor = AddWorktree(repository.Path, "warm-linked-build-donor");
        WriteCache(donor, "preserve donor\n");
        _ = WriteProjectOlean(donor, "WarmDonor");
        var fixture = new MissingStampDonorTargetFixture(donor, repository.Path);
        fixture.CreateLake();
        fixture.WriteTargetOwned("preserve main\n");
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner
        {
            Results = new Queue<DirectoryCloneResult>(
                [new(false, false, 18, 1, "cross-device clone")]),
            AfterClone = (_, staged) => Directory.CreateDirectory(staged),
        };

        var result = withWriter
            ? LeanCacheEnsureCommand.RunWithWriter(repository.Path,
                ["--", "lake", "build"], runner, cloner,
                FileSystemLeanCacheStateProbe.Instance,
                _ => "1")
            : WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner, cloner);

        Assert.False(result.Success);
        Assert.Equal(fixture.DonorBuild, Assert.Single(cloner.Invocations).Source);
        Assert.DoesNotContain(runner.Invocations, static call => call.FileName == "cp"
            || Path.GetFileName(call.FileName) == "lake");
        Assert.Equal(0, runner.ArchiveInvocations);
        Assert.Equal("preserve main\n", fixture.TargetOwnedText);
        Assert.Equal("preserve donor\n", LeanCacheFixtureFile.ReadCacheText(donor));
        Assert.False(fixture.BuildDirectoryExists);
        Assert.False(fixture.TargetStampExists);
        Assert.Empty(fixture.BuildStageDirectories);
        using var receipt = ParseReceipt(result.Error);
        Assert.Equal("failed", receipt.RootElement.GetProperty("status").GetString());
        AssertCrossDeviceCloneReceipt(receipt.RootElement);
    }
}
