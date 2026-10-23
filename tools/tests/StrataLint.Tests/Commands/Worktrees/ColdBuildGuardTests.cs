using StrataLint.Cli;
using System.Text.Json;

namespace StrataLint.Tests;

public sealed partial class WorktreeCommandTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ProjectColdWithoutConsentRejectsWrappedBuildWithExecutableCacheCommand(bool mathlibWarm)
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var runner = new RecordingWorktreeProcessRunner { OmitMathlibOleans = !mathlibWarm };

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
        Assert.Equal(mathlibWarm ? "warm" : "cold", receipt.RootElement.GetProperty("mathlib_olean_state").GetString());
        Assert.Equal("cold", receipt.RootElement.GetProperty("project_olean_state").GetString());
        Assert.Equal(JsonValueKind.Null, receipt.RootElement.GetProperty("mathlib_olean_probe_error").ValueKind);
        Assert.Equal(JsonValueKind.Null, receipt.RootElement.GetProperty("project_olean_probe_error").ValueKind);
    }

    [Theory]
    [InlineData(false, "with-cache-reader")]
    [InlineData(true, "with-cache-reader")]
    [InlineData(false, "with-cache-writer")]
    [InlineData(true, "with-cache-writer")]
    public void ProjectColdWithExactConsentRunsWrappedBuildAndRecordsConsentInReceipt(bool mathlibWarm, string entry)
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var runner = new RecordingWorktreeProcessRunner { OmitMathlibOleans = !mathlibWarm };

        var result = WithColdBuildConsent(
            "1",
            () => WorktreeCommand.Run(
                repository.Path,
                [entry, "--", "lake", "build"],
                runner));

        Assert.True(result.Success, result.Error);
        Assert.Single(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
        using var receipt = ParseReceipt(result.Output);
        Assert.True(receipt.RootElement.GetProperty("cold_build_consent").GetBoolean());
        Assert.Equal("cold", receipt.RootElement.GetProperty("project_olean_state").GetString());
        Assert.Equal(mathlibWarm ? "warm" : "cold", receipt.RootElement.GetProperty("mathlib_olean_state").GetString());
    }

    [Theory]
    [InlineData(false, "true")]
    [InlineData(true, "true")]
    [InlineData(false, " 1")]
    [InlineData(true, " 1")]
    [InlineData(false, "1 ")]
    [InlineData(true, "1 ")]
    [InlineData(false, "01")]
    [InlineData(true, "01")]
    [InlineData(false, "")]
    [InlineData(true, "")]
    public void ProjectColdWithInexactConsentStillRejectsWrappedBuild(bool mathlibWarm, string consent)
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var runner = new RecordingWorktreeProcessRunner { OmitMathlibOleans = !mathlibWarm };

        var result = WithColdBuildConsent(
            consent,
            () => WorktreeCommand.Run(
                repository.Path,
                ["with-cache-writer", "--", "lake", "build"],
                runner));

        Assert.False(result.Success);
        Assert.DoesNotContain(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void KnownProjectWarmRunsWrappedBuildWithoutReadingColdConsent(bool mathlibWarm)
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        _ = ProjectOleanFixture.Write(repository.Path, "ExistingProject");
        var runner = new RecordingWorktreeProcessRunner { OmitMathlibOleans = !mathlibWarm };

        var result = LeanCacheEnsureCommand.RunWithWriter(
            repository.Path,
            ["--", "lake", "build"],
            runner,
            new RecordingDirectoryCloner(),
            FileSystemLeanCacheStateProbe.Instance,
            _ => throw new InvalidOperationException("consent must not be read on a known Project Warm path"));

        Assert.True(result.Success, result.Error);
        Assert.Single(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("warm", receipt.RootElement.GetProperty("project_olean_state").GetString());
        Assert.Equal(mathlibWarm ? "warm" : "cold", receipt.RootElement.GetProperty("mathlib_olean_state").GetString());
        Assert.False(receipt.RootElement.TryGetProperty("cold_build_consent", out _));
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
            _ => throw new InvalidOperationException("consent cannot authorize an unknown probe"));

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
        Assert.Contains("sync dev and warm the dev cache", result.Error, StringComparison.Ordinal);
        using var failure = ParseReceipt(result.Error);
        Assert.Contains(
            $"make -C '{LeanCacheGuard.PhysicalPath(repository.Path)}' warm-donor",
            failure.RootElement.GetProperty("reason").GetString(),
            StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(true, false, null)]
    [InlineData(true, false, "1")]
    [InlineData(false, true, null)]
    [InlineData(false, true, "1")]
    [InlineData(true, true, null)]
    [InlineData(true, true, "1")]
    public void EitherProbeFailureRefusesEvenWithConsentAndTheOtherLayerWarm(
        bool mathlibFailed, bool projectFailed, string? consent)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        StampCache(repository.Path);
        _ = ProjectOleanFixture.Write(repository.Path, "ExistingProject");
        var projectRoot = Path.Combine(repository.Path, ".lake", "build", "lib", "lean");
        var probe = new DelegatingLeanCacheStateProbe(root =>
        {
            var failed = root == projectRoot ? projectFailed : mathlibFailed;
            return new OleanWarmthInspection(
                failed ? OleanWarmth.ProbeFailed : OleanWarmth.Warm,
                failed ? "injected enumeration failure" : null);
        });
        var runner = new RecordingWorktreeProcessRunner();
        var environmentReads = 0;

        var result = LeanCacheEnsureCommand.RunWithWriter(
            repository.Path, ["--", "lake", "build"], runner,
            new RecordingDirectoryCloner(), probe,
            _ => { environmentReads++; return consent; });

        Assert.False(result.Success);
        Assert.Equal(0, environmentReads);
        Assert.Contains("probe failed", result.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("To accept", result.Error, StringComparison.Ordinal);
        Assert.DoesNotContain(runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal(mathlibFailed ? "probe_failed" : "warm",
            receipt.RootElement.GetProperty("mathlib_olean_state").GetString());
        Assert.Equal(projectFailed ? "probe_failed" : "warm",
            receipt.RootElement.GetProperty("project_olean_state").GetString());
        Assert.False(receipt.RootElement.TryGetProperty("cold_build_consent", out _));
        Assert.Equal(1, probe.Count(projectRoot));
        Assert.Equal(1, probe.Count(Path.Combine(repository.Path,
            ".lake", "packages", "mathlib", ".lake", "build", "lib", "lean")));
        using var released = LeanCacheWriterGuard.TryAcquire(Path.Combine(repository.Path, ".lake"));
        Assert.NotNull(released);
    }

    [Theory]
    [InlineData(null, 21600)]
    [InlineData("invalid", 21600)]
    [InlineData("5400", 5400)]
    [InlineData("1", 300)]
    [InlineData("300", 300)]
    [InlineData("21600", 21600)]
    [InlineData("30000", 21600)]
    public void ConsentedWrappedBuildReceivesTheBoundedCommandCutoff(string? raw, int expectedSeconds)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        StampCache(repository.Path);
        Directory.CreateDirectory(Path.Combine(repository.Path, ".lake", "build", "retained"));
        var runner = new RecordingWorktreeProcessRunner();
        var previous = Environment.GetEnvironmentVariable("STRATALINT_LEAN_CACHE_TIMEOUT_SECONDS");
        try
        {
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_CACHE_TIMEOUT_SECONDS", raw);
            var result = LeanCacheEnsureCommand.RunWithWriter(
                repository.Path, ["--", "lake", "build"], runner,
                new RecordingDirectoryCloner(), FileSystemLeanCacheStateProbe.Instance, _ => "1");

            Assert.True(result.Success, result.Error);
            var invoked = Assert.Single(runner.Invocations,
                static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
            Assert.Equal(expectedSeconds, invoked.Timeout.TotalSeconds);
            using var receipt = ParseReceipt(result.Output);
            Assert.True(receipt.RootElement.GetProperty("cold_build_consent").GetBoolean());
        }
        finally
        {
            Environment.SetEnvironmentVariable("STRATALINT_LEAN_CACHE_TIMEOUT_SECONDS", previous);
        }
    }

    [Fact]
    public void AdmittedWrappedTimeoutPreservesFailureReceiptAndReleasesWriterGuard()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        StampCache(repository.Path);
        _ = ProjectOleanFixture.Write(repository.Path, "ExistingProject");
        var runner = new RecordingWorktreeProcessRunner
        {
            DuringWrappedLake = _ => throw new TimeoutException("wrapped command timed out"),
        };

        var result = LeanCacheEnsureCommand.RunWithWriter(
            repository.Path, ["--", "lake", "build"], runner,
            new RecordingDirectoryCloner(), FileSystemLeanCacheStateProbe.Instance,
            _ => throw new InvalidOperationException("known Project Warm does not read consent"));

        Assert.False(result.Success);
        Assert.Contains("wrapped command timed out", result.Error, StringComparison.Ordinal);
        Assert.Single(runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("warm", receipt.RootElement.GetProperty("project_olean_state").GetString());
        using var released = LeanCacheWriterGuard.TryAcquire(Path.Combine(repository.Path, ".lake"));
        Assert.NotNull(released);
    }

    [Theory]
    [InlineData("with-cache-reader", false, "", false, 0)]
    [InlineData("with-cache-writer", false, "", false, 0)]
    [InlineData("with-cache-reader", false, "1", true, 23)]
    [InlineData("with-cache-writer", false, "1", true, 124)]
    [InlineData("with-cache-reader", true, "", true, 0)]
    [InlineData("with-cache-writer", true, "", true, 0)]
    public void ProductionLeafReaderAndWriterAliasObserveActualWrappedCommandAndExit(
        string entry, bool projectWarm, string consent, bool admitted, int commandExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new PrivateReaderFixture();
        InitializeRepository(fixture.Reader);
        StampCache(fixture.Reader);
        if (!projectWarm)
            File.Delete(Path.Combine(fixture.Reader, ".lake", "build", "lib", "lean", "Fixture.olean"));
        var marker = Path.Combine(fixture.Reader, "wrapped-command-ran");

        var result = TestProcessRunner.Run("/usr/bin/env",
            ["LAKE_BIN=" + fixture.Lake, "STRATALINT_ACCEPT_COLD_BUILD=" + consent,
                "dotnet", typeof(LeanProgram).Assembly.Location, entry, "--path", fixture.Reader, "--",
                "/bin/sh", "-c", "printf 'command-output\\n'; printf 'command-error\\n' >&2; printf ran > \"$1\"; exit \"$2\"",
                "guard-test", marker, commandExit.ToString(System.Globalization.CultureInfo.InvariantCulture)],
            fixture.Reader, TestBudgets.ScriptProcessHangGuard, 64 * 1024);

        Assert.Equal(admitted ? commandExit : 2, result.ExitCode);
        Assert.Equal(admitted, File.Exists(marker));
        var output = System.Text.Encoding.UTF8.GetString(result.StandardOutput);
        var error = System.Text.Encoding.UTF8.GetString(result.StandardError);
        if (admitted)
        {
            Assert.Equal("ran", File.ReadAllText(marker));
            Assert.EndsWith("command-output\n", output, StringComparison.Ordinal);
            Assert.Equal("command-error\n", error);
            using var receipt = ParseReceipt(output[..(output.IndexOf('\n', StringComparison.Ordinal) + 1)]);
            if (!projectWarm) Assert.True(receipt.RootElement.GetProperty("cold_build_consent").GetBoolean());
        }
        else
        {
            Assert.DoesNotContain("command-output", output, StringComparison.Ordinal);
            Assert.Contains("COLD_BUILD_REFUSED project olean cache is cold", error, StringComparison.Ordinal);
            Assert.Contains(fixture.Reader, error, StringComparison.Ordinal);
        }
        using var released = LeanCacheWriterGuard.TryAcquire(Path.Combine(fixture.Reader, ".lake"));
        Assert.NotNull(released);
    }

    [Theory]
    [InlineData("30", 23)]
    [InlineData("0", 124)]
    public void ProductionLeafSharesCiComputeAllowanceAndReleasesWriter(string remaining, int expectedExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new PrivateReaderFixture();
        InitializeRepository(fixture.Reader);
        StampCache(fixture.Reader);
        var budget = Path.Combine(fixture.Reader, "compute-seconds");
        File.WriteAllText(budget, remaining);
        var helper = Path.Combine(fixture.Reader, "tools/scripts/workflow/ci_compute.py");
        Directory.CreateDirectory(Path.GetDirectoryName(helper)!);
        File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/workflow/ci_compute.py"), helper);
        var marker = Path.Combine(fixture.Reader, "command-ran");
        var result = TestProcessRunner.Run("/usr/bin/env",
            ["STRATALINT_CI_COMPUTE_ACTIVE=0", "STRATALINT_CI_COMPUTE_BUDGET=" + budget,
                "LAKE_BIN=" + fixture.Lake, "dotnet", typeof(LeanProgram).Assembly.Location,
                "with-cache-reader", "--path", fixture.Reader, "--", "/bin/sh", "-c",
                "printf ran > \"$1\"; exit 23", "compute-test", marker],
            fixture.Reader, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
        Assert.Equal(expectedExit, result.ExitCode);
        Assert.Equal(expectedExit == 23, File.Exists(marker));
        using var released = LeanCacheWriterGuard.TryAcquire(Path.Combine(fixture.Reader, ".lake"));
        Assert.NotNull(released);
    }

    private static string AddColdGuardWorktree(string repositoryRoot, string name)
    {
        var target = Path.Combine(repositoryRoot, name);
        _ = TestGit.Run(
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
