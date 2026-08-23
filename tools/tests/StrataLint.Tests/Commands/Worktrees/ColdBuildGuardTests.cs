using StrataLint.Cli;
using System.Text.Json;

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
        Assert.Contains("make -C", result.Error, StringComparison.Ordinal);
        Assert.Contains(repository.Path, result.Error, StringComparison.Ordinal);
        Assert.Contains("lean-cache-ensure", result.Error, StringComparison.Ordinal);
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("cold", receipt.RootElement.GetProperty("mathlib_olean_state").GetString());
        Assert.Equal("cold", receipt.RootElement.GetProperty("project_olean_state").GetString());
        Assert.Equal(JsonValueKind.Null, receipt.RootElement.GetProperty("mathlib_olean_probe_error").ValueKind);
        Assert.Equal(JsonValueKind.Null, receipt.RootElement.GetProperty("project_olean_probe_error").ValueKind);
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
    public void OleanEnumerationFailuresAreReportedAsProbeFailuresAndRejectWrappedBuild()
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
        Assert.Contains("make -C", result.Error, StringComparison.Ordinal);
        Assert.Contains(repository.Path, result.Error, StringComparison.Ordinal);
        Assert.Contains("lean-cache-ensure", result.Error, StringComparison.Ordinal);
        Assert.Contains("probe failed", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("both cold", result.Error, StringComparison.OrdinalIgnoreCase);
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("probe_failed", receipt.RootElement.GetProperty("mathlib_olean_state").GetString());
        Assert.Equal("probe_failed", receipt.RootElement.GetProperty("project_olean_state").GetString());
        Assert.Contains(
            "injected enumeration failure",
            receipt.RootElement.GetProperty("mathlib_olean_probe_error").GetString()!,
            StringComparison.Ordinal);
        Assert.Contains(
            "injected enumeration failure",
            receipt.RootElement.GetProperty("project_olean_probe_error").GetString()!,
            StringComparison.Ordinal);
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

    [Fact]
    public void PathTargetedColdBuildRefusalInstructionsNameRejectedWorktreeWhenCwdDiffers()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var target = AddColdGuardWorktree(repository.Path, "path-targeted-cold-refusal");
        var runner = new RecordingWorktreeProcessRunner { OmitMathlibOleans = true };

        var result = LeanCacheEnsureCommand.RunWithWriter(
            repository.Path,
            ["--path", target, "--", "lake", "build"],
            runner,
            new RecordingDirectoryCloner(),
            FileSystemLeanCacheStateProbe.Instance,
            _ => null);

        Assert.False(result.Success);
        Assert.Contains(target, result.Error, StringComparison.Ordinal);
        Assert.Contains("make -C", result.Error, StringComparison.Ordinal);
        Assert.Contains("lean-cache-ensure", result.Error, StringComparison.Ordinal);
        Assert.Contains("STRATALINT_ACCEPT_COLD_BUILD=1", result.Error, StringComparison.Ordinal);
    }

    private static string AddColdGuardWorktree(string repositoryRoot, string name)
    {
        var target = Path.Combine(repositoryRoot, name);
        _ = ReviewRegressionTests.RunGit(
            repositoryRoot,
            ["worktree", "add", "-b", $"harness/{name}", target, "HEAD"]);
        return target;
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
