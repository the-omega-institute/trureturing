using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class LeanCacheEnsureCommandTests
{
    [Theory]
    [InlineData("with-cache-reader", false)]
    [InlineData("with-cache-reader", true)]
    [InlineData("with-cache-writer", false)]
    [InlineData("with-cache-writer", true)]
    public void WrappedWarmBuildReusesMatchingCacheWithoutReleaseRefresh(string entry, bool buildFails)
    {
        using var repository = new TemporaryDirectory();
        var fixture = new EnsureArchiveFixture(repository.Path, "warm-build");
        fixture.WriteProjectOlean();
        MathlibProjectionFixture.Write(Path.Combine(fixture.Target, ".lake"));
        var olean = Path.Combine(fixture.Target, ".lake", "build", "lib", "lean", "Warm.olean");
        File.SetLastWriteTimeUtc(olean, TestEnvironmentBridge.UtcNow().AddHours(-7));
        var originalTime = File.GetLastWriteTimeUtc(olean);
        var writerHeldDuringBuild = false;
        var runner = new RecordingWorktreeProcessRunner
        {
            FailWrappedLake = buildFails,
            DuringWrappedLake = root =>
            {
                using var otherWriter = LeanCacheWriterGuard.TryAcquire(Path.Combine(root, ".lake"));
                writerHeldDuringBuild = otherWriter is null;
            },
            AfterArchiveFetch = _ => throw new Xunit.Sdk.XunitException("warm build must reuse its cache"),
        };

        var result = WorktreeCommand.Run(fixture.Target,
            [entry, "--", "lake", "--log-level=error", "build", "D5.Target"], runner);

        Assert.Equal(!buildFails, result.Success);
        Assert.Equal(buildFails ? 1 : 0, result.ExitCode);
        Assert.Equal(0, runner.ArchiveInvocations);
        Assert.Single(runner.Invocations, call => call.FileName == "lake"
            && call.Arguments.SequenceEqual(["--log-level=error", "build", "D5.Target"]));
        Assert.True(writerHeldDuringBuild);
        Assert.Equal("warm\n", File.ReadAllText(olean));
        Assert.Equal(originalTime, File.GetLastWriteTimeUtc(olean));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("present", receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal("not_attempted", receipt.RootElement.GetProperty("archive_status").GetString());
        Assert.Equal("warm", receipt.RootElement.GetProperty("mathlib_olean_state").GetString());
        Assert.Equal("warm", receipt.RootElement.GetProperty("project_olean_state").GetString());
    }

    [Theory]
    [InlineData("with-cache-reader")]
    [InlineData("with-cache-writer")]
    public void WrappedColdBuildStillFetchesProjectArchive(string entry)
    {
        using var repository = new TemporaryDirectory();
        var fixture = new EnsureArchiveFixture(repository.Path, "cold-build");
        MathlibProjectionFixture.Write(Path.Combine(fixture.Target, ".lake"));
        var runner = new RecordingWorktreeProcessRunner
        {
            ArchiveReceipt = "LEAN_CACHE_FETCH {\"status\":\"unpacked\",\"mode\":\"partition\"}\n",
            AfterArchiveFetch = _ => fixture.WriteProjectOlean(),
        };

        var result = WorktreeCommand.Run(fixture.Target, [entry, "--", "lake", "build", "D5.Target"], runner);

        var receipt = ReadReceipt(result);
        Assert.Equal(1, runner.ArchiveInvocations);
        Assert.Equal("unpacked", receipt.GetProperty("archive_status").GetString());
        Assert.Single(runner.Invocations, call => call.FileName == "lake"
            && call.Arguments.SequenceEqual(["build", "D5.Target"]));
    }

    [Theory]
    [InlineData("with-cache-reader", false)]
    [InlineData("with-cache-writer", false)]
    [InlineData("with-cache-reader", true)]
    [InlineData("with-cache-writer", true)]
    public void WrappedBuildStillRefreshesWhenMathlibIsCold(string entry, bool installsArchive)
    {
        using var repository = new TemporaryDirectory();
        var fixture = new EnsureArchiveFixture(repository.Path, "cold-mathlib-build");
        fixture.WriteProjectOlean();
        File.SetLastWriteTimeUtc(Path.Combine(fixture.Target, ".lake", "build", "lib", "lean", "Warm.olean"),
            TestEnvironmentBridge.UtcNow().AddHours(-7));
        var runner = new RecordingWorktreeProcessRunner
        {
            ArchiveReceipt = installsArchive
                ? "LEAN_CACHE_FETCH {\"status\":\"unpacked\",\"mode\":\"partition\"}\n"
                : "LEAN_CACHE_FETCH {\"status\":\"miss\",\"reason\":\"offline\"}\n",
            ArchiveExitCode = installsArchive ? 0 : 1,
            AfterArchiveFetch = installsArchive
                ? _ => MathlibProjectionFixture.Write(Path.Combine(fixture.Target, ".lake")) : null,
        };

        var result = WorktreeCommand.Run(fixture.Target, [entry, "--", "lake", "build", "D5.Target"], runner);

        var receipt = ReadReceipt(result);
        Assert.Equal(1, runner.ArchiveInvocations);
        Assert.Contains("--refresh-stale", Assert.Single(runner.Invocations,
            call => call.FileName == "/bin/bash").Arguments);
        Assert.Equal(installsArchive ? "unpacked" : "miss", receipt.GetProperty("archive_status").GetString());
        Assert.Equal(installsArchive ? "warm" : "cold", receipt.GetProperty("mathlib_olean_state").GetString());
    }
}
