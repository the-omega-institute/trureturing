using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class WorktreeCommandTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MissingOrFailedCacheSupplyAlwaysEntersWrappedBuild(bool failCache)
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var runner = new RecordingWorktreeProcessRunner { OmitMathlibOleans = true, FailLake = failCache };

        var result = WorktreeCommand.Run(repository.Path, ["with-cache-writer", "--", "lake", "build"], runner);

        Assert.True(result.Success, result.Error);
        Assert.Contains(runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("cold", receipt.RootElement.GetProperty("mathlib_olean_state").GetString());
        Assert.Equal("cold", receipt.RootElement.GetProperty("project_olean_state").GetString());
    }

    [Fact]
    public void OleanProbeFailureIsReportedAndStillEntersNormalBuild()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var runner = new RecordingWorktreeProcessRunner();
        var probe = new DelegatingLeanCacheStateProbe(
            _ => new OleanWarmthInspection(OleanWarmth.ProbeFailed, "injected enumeration failure"));

        var result = LeanCacheEnsureCommand.RunWithWriter(repository.Path, ["--", "lake", "build"],
            runner, new RecordingDirectoryCloner(), probe);

        Assert.True(result.Success, result.Error);
        Assert.Contains(runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("probe_failed", receipt.RootElement.GetProperty("mathlib_olean_state").GetString());
        Assert.Equal("probe_failed", receipt.RootElement.GetProperty("project_olean_state").GetString());
        Assert.Equal(1, probe.Count(Path.Combine(repository.Path, ".lake", "build", "lib", "lean")));
    }
}

internal static class ProjectOleanFixture
{
    internal static string Write(string root, string name)
    {
        var path = Path.Combine(root, ".lake", "build", "lib", "lean", name + ".olean");
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, name + "\n");
        return path;
    }
}
