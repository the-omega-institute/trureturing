using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class WorktreeCommandTests
{
    [Fact]
    public void AllColdWithoutConsentRejectsWrappedBuildWithExecutableCacheCommand()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var runner = new RecordingWorktreeProcessRunner { OmitMathlibOleans = true };

        var result = WithColdBuildConsent(
            null,
            () => WorktreeCommand.Run(
                repository.Path,
                ["with-cache-writer", "--", "lake", "build"],
                runner));

        Assert.False(result.Success);
        Assert.DoesNotContain(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
        Assert.Contains("make lean-cache-ensure", result.Output + result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void AllColdWithExactConsentRunsWrappedBuildAndRecordsConsentInReceipt()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var runner = new RecordingWorktreeProcessRunner { OmitMathlibOleans = true };

        var result = WithColdBuildConsent(
            "1",
            () => WorktreeCommand.Run(
                repository.Path,
                ["with-cache-writer", "--", "lake", "build"],
                runner));

        Assert.True(result.Success, result.Error);
        Assert.Contains(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
        using var receipt = ParseReceipt(result.Output);
        Assert.True(receipt.RootElement.GetProperty("cold_build_consent").GetBoolean());
    }

    [Fact]
    public void AllColdWithTruthyButInexactConsentStillRejectsWrappedBuild()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var runner = new RecordingWorktreeProcessRunner { OmitMathlibOleans = true };

        var result = WithColdBuildConsent(
            "true",
            () => WorktreeCommand.Run(
                repository.Path,
                ["with-cache-writer", "--", "lake", "build"],
                runner));

        Assert.False(result.Success);
        Assert.DoesNotContain(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
    }

    [Fact]
    public void WarmMathlibRunsWrappedBuildWithoutReadingColdConsent()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var runner = new RecordingWorktreeProcessRunner();
        var environmentReads = 0;

        var result = LeanCacheEnsureCommand.RunWithWriter(
            repository.Path,
            ["--", "lake", "build"],
            runner,
            new RecordingDirectoryCloner(),
            FileSystemLeanCacheStateProbe.Instance,
            _ =>
            {
                environmentReads++;
                return "1";
            });

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, environmentReads);
        Assert.Contains(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
    }

    [Fact]
    public void WarmProjectRunsWrappedBuildWhenMathlibIsColdWithoutReadingConsent()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        _ = ProjectOleanFixture.Write(repository.Path, "ExistingProject");
        var runner = new RecordingWorktreeProcessRunner { OmitMathlibOleans = true };

        var result = LeanCacheEnsureCommand.RunWithWriter(
            repository.Path,
            ["--", "lake", "build"],
            runner,
            new RecordingDirectoryCloner(),
            FileSystemLeanCacheStateProbe.Instance,
            _ => throw new InvalidOperationException("consent must not be read on a warm path"));

        Assert.True(result.Success, result.Error);
        Assert.Contains(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
    }

    [Fact]
    public void OleanEnumerationFailuresAreTreatedAsColdAndRejectWrappedBuild()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var runner = new RecordingWorktreeProcessRunner();
        var probe = new DelegatingLeanCacheStateProbe(
            _ => new OleanWarmthInspection(OleanWarmth.ProbeFailed, "injected enumeration failure"));

        var result = LeanCacheEnsureCommand.RunWithWriter(
            repository.Path,
            ["--", "lake", "build"],
            runner,
            new RecordingDirectoryCloner(),
            probe,
            _ => null);

        Assert.False(result.Success);
        Assert.DoesNotContain(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
        Assert.Contains("make lean-cache-ensure", result.Output + result.Error, StringComparison.Ordinal);
        Assert.Equal(1, probe.Count(Path.Combine(repository.Path, ".lake", "build", "lib", "lean")));
        Assert.Equal(1, probe.Count(Path.Combine(
            repository.Path,
            ".lake",
            "packages",
            "mathlib",
            ".lake",
            "build",
            "lib",
            "lean")));
    }

    private static CommandResult WithColdBuildConsent(string? value, Func<CommandResult> action)
    {
        var previous = Environment.GetEnvironmentVariable("STRATALINT_ACCEPT_COLD_BUILD");
        try
        {
            Environment.SetEnvironmentVariable("STRATALINT_ACCEPT_COLD_BUILD", value);
            return action();
        }
        finally
        {
            Environment.SetEnvironmentVariable("STRATALINT_ACCEPT_COLD_BUILD", previous);
        }
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
