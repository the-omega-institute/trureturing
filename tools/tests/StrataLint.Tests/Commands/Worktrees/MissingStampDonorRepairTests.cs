using StrataLint.Cli;

namespace StrataLint.Tests;

// Missing-stamp additive recovery must preserve prior output across publication failures.
public sealed partial class LeanCacheEnsureCommandTests
{
    [Fact]
    public void MissingStampWithEmptyBuildRootAddsBuildAndPackagesWithoutReplacingLake()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var fixture = new MissingStampDonorTargetFixture(
            repository.Path,
            AddWorktree(repository.Path, "empty-build-root-target"));
        fixture.CreateLake();
        fixture.CreateEmptyBuildRoot();
        fixture.WriteTargetOwned("retained empty-build lane\n");
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", fixture.Target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.Equal(2, cloner.Invocations.Count);
        Assert.Equal("retained empty-build lane\n", fixture.TargetOwnedText);
        Assert.True(fixture.TargetPackagesExist);
        Assert.Empty(fixture.BuildStageDirectories);
        Assert.True(fixture.BuildCacheExists);
        Assert.True(fixture.BuildDirectoryExists);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void StampWriteFailurePreservesAllArtifactsThroughOrdinaryEnsureRetry(bool existingBuild)
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var fixture = new MissingStampDonorTargetFixture(
            repository.Path,
            AddWorktree(repository.Path, "missing-build-stamp-write-failure"));
        fixture.CreateLake();
        WriteRestoreFixture(fixture.Lake, "packages/target-only/source.lean", "target-only package");
        WriteRestoreFixture(fixture.Lake, "packages/mathlib/.lake/build/lib/lean/TargetOnly.olean", "target-only compiler");
        WriteRestoreFixture(fixture.Lake, "stratalint/raw-lean-report.json", "target-only report");
        if (existingBuild)
        {
            WriteSplitOwnership(fixture.Target);
            _ = WriteFormerOwners(fixture.Target);
            WriteRestoreFixture(fixture.Lake, "build/lib/lean/TargetOnly.olean", "project compiler");
            WriteRestoreFixture(fixture.Lake, "build/stratalint/raw-lean-report.json", "project report");
        }
        var before = Directory.GetFiles(fixture.Lake, "*", SearchOption.AllDirectories)
            .ToDictionary(path => path, File.ReadAllBytes);
        var failedCloner = new RecordingDirectoryCloner();

        var exception = Assert.Throws<LeanCacheProvisionException>(
            () => fixture.ProvisionWithFailingStampWrite(
                new RecordingWorktreeProcessRunner(),
                failedCloner));

        Assert.Contains("injected stamp write failure", exception.Message, StringComparison.Ordinal);
        Assert.Equal(2, failedCloner.Invocations.Count);
        foreach (var (path, bytes) in before) Assert.Equal(bytes, File.ReadAllBytes(path));

        // The overlay provisioner leaves a published-but-unstamped tree when stamp writing fails.
        Assert.True(fixture.BuildDirectoryExists);
        Assert.True(fixture.BuildCacheExists);
        Assert.False(fixture.TargetStampExists);

        var published = Directory.GetFiles(fixture.Lake, "*", SearchOption.AllDirectories)
            .ToDictionary(path => path, File.ReadAllBytes);
        // Missing compatible material on continuation must be added, not just stamped.
        WriteRestoreFixture(Path.Combine(repository.Path, ".lake/packages/mathlib"),
            "Mathlib/AddedOnRetry.lean", "added dependency");
        var retryCloner = new RecordingDirectoryCloner();
        var retry = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", fixture.Target],
            new RecordingWorktreeProcessRunner(),
            retryCloner);

        // Ordinary canonical retry remains additive after the stamp I/O boundary is repaired.
        Assert.True(retry.Success, retry.Error);
        foreach (var (path, bytes) in published) Assert.Equal(bytes, File.ReadAllBytes(path));
        Assert.Equal(2, retryCloner.Invocations.Count);
        Assert.Equal("added dependency", File.ReadAllText(Path.Combine(fixture.Lake,
            "packages/mathlib/Mathlib/AddedOnRetry.lean")));
        Assert.Empty(Directory.GetDirectories(fixture.Lake, "*.stage-*"));
        Assert.True(fixture.BuildCacheExists);
        Assert.True(fixture.StampMatches);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MissingStampRefusesNonPrivateExistingBuildPreservingly(bool symlink)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "donor", projectWarm: true);
        var target = AddWorktree(repository.Path, "nonprivate-build");
        var lake = Path.Combine(target, ".lake");
        WriteRestoreFixture(lake, "target-owned", "retained");
        var build = Path.Combine(lake, "build");
        if (symlink) Directory.CreateSymbolicLink(build, Path.Combine(repository.Path, ".lake/build"));
        else File.WriteAllText(build, "retained conflicting file");
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(), cloner);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Equal("retained", File.ReadAllText(Path.Combine(lake, "target-owned")));
        if (symlink) Assert.True(File.GetAttributes(build).HasFlag(FileAttributes.ReparsePoint));
        else Assert.Equal("retained conflicting file", File.ReadAllText(build));
        Assert.Equal("donor", LeanCacheFixtureFile.ReadCacheText(repository.Path));
        Assert.False(File.Exists(LeanCacheStamp.PathFor(lake)));
        Assert.Empty(Directory.GetDirectories(lake, "*.stage-*"));
        Assert.Contains("lean-cache-ensure", ReceiptReason(result.Error), StringComparison.Ordinal);
    }

    [Fact]
    public void MissingStampBuildConflictRemainsAuthoritativeAndReceiptReportsActualWarmth()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "donor", projectWarm: true);
        var target = AddWorktree(repository.Path, "conflicting-build-facet");
        var lake = Path.Combine(target, ".lake");
        WriteRestoreFixture(lake, "build/lib", "retained incomplete facet");

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(), new RecordingDirectoryCloner());

        Assert.True(result.Success, result.Error);
        Assert.Equal("retained incomplete facet", File.ReadAllText(Path.Combine(lake, "build/lib")));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("cold", receipt.RootElement.GetProperty("project_olean_state").GetString());
        Assert.Contains("native Lake must validate", ReceiptReason(result.Output), StringComparison.Ordinal);
    }
}
