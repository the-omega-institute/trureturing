using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class WorktreeCommandWriterTests
{
    [Theory]
    [InlineData("miss", false)]
    [InlineData("corrupt", false)]
    [InlineData("timeout", false)]
    [InlineData("miss", true)]
    [InlineData("corrupt", true)]
    [InlineData("timeout", true)]
    public void OptionalArchiveFailureReachesBuildWithItsOwnBudget(string failure, bool buildFails)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new SharedLakeFixture(native: true);
        var root = fixture.Reader;
        var script = LeanArchiveFetch.ScriptPath(root);
        Directory.CreateDirectory(Path.GetDirectoryName(script)!);
        File.WriteAllText(script, "#!/bin/sh\nexit 0\n");
        if (buildFails) File.WriteAllText(Path.Combine(root, "Fixture.lean"), "unknown_command\n");
        var runner = new ArchiveFaultRunner(fixture.LockDirectory, failure);

        var result = LeanCacheEnsureCommand.Run(root, ["--", "lake", "build"], runner, runCommand: true);

        Assert.True(result.Success == !buildFails, result.Output + result.Error);
        Assert.Equal(1, runner.Archives);
        Assert.Equal(1, runner.Builds);
        Assert.True(runner.BuildAfterArchive);
        Assert.Contains("\"archive_status\":\"" + (failure == "miss" ? "miss" : "failed") + "\"", result.Output);
        Assert.Equal(
            LeanCacheBudgetPolicy.LeanInspectJobBudgetMinutes - LeanCacheBudgetPolicy.PostArchiveReserveMinutes,
            runner.ArchiveBudget.TotalMinutes);
        Assert.Equal(LeanCacheProvisioner.LeanCommandBudget, runner.BuildBudget);
        if (buildFails) Assert.Equal(1, result.ExitCode);
        else Assert.True(File.Exists(Path.Combine(root, ".lake", "build", "lib", "lean", "Fixture.olean")));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RestoredProjectSeedBypassesArchiveAndStillRunsBuild(bool buildFails)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new SharedLakeFixture(native: true);
        var root = fixture.Reader;
        var build = Path.Combine(root, ".lake", "build");
        Directory.CreateDirectory(build);
        File.WriteAllText(Path.Combine(build, "seed-marker"), "retained");
        var script = LeanArchiveFetch.ScriptPath(root);
        Directory.CreateDirectory(Path.GetDirectoryName(script)!);
        File.WriteAllText(script, "#!/bin/sh\nexit 0\n");
        if (buildFails) File.WriteAllText(Path.Combine(root, "Fixture.lean"), "unknown_command\n");
        var runner = new ArchiveFaultRunner(fixture.LockDirectory, "unused");

        var result = LeanCacheEnsureCommand.Run(root, ["--", "lake", "build"], runner, runCommand: true);

        Assert.True(result.Success == !buildFails, result.Output + result.Error);
        Assert.Equal(0, runner.Archives);
        Assert.Equal(1, runner.Builds);
        Assert.Equal("retained", File.ReadAllText(Path.Combine(build, "seed-marker")));
        Assert.Contains("\"archive_status\":\"notattempted\"", result.Output);
    }

    private sealed class ArchiveFaultRunner(string lockDirectory, string fault) : IWorktreeProcessRunner
    {
        private readonly ProductionWorktreeProcessRunner native = new();
        internal int Archives { get; private set; }
        internal int Builds { get; private set; }
        internal bool BuildAfterArchive { get; private set; }
        internal TimeSpan ArchiveBudget { get; private set; }
        internal TimeSpan BuildBudget { get; private set; }

        public ProcessOutput Run(string file, IReadOnlyList<string> arguments, string root, TimeSpan budget) =>
            native.Run(file, arguments, root, budget);

        public ProcessOutput RunWithEnvironment(string file, IReadOnlyList<string> arguments, string root,
            TimeSpan budget, IReadOnlyDictionary<string, string> environment)
        {
            if (arguments.Contains("--writer-owned"))
            {
                Archives++;
                ArchiveBudget = budget;
                using var concurrent = LeanCacheWriterGuard.TryAcquire(Path.Combine(root, ".lake"), lockDirectory);
                Assert.Null(concurrent);
                if (fault == "timeout") throw new TimeoutException("fixture archive deadline expired");
                var receipt = fault == "corrupt" ? "broken receipt\n"
                    : "LEAN_CACHE_FETCH {\"status\":\"miss\",\"reason\":\"fixture\"}\n";
                return new(1, Encoding.UTF8.GetBytes(receipt), []);
            }
            if (arguments.LastOrDefault() == "build")
            {
                Builds++;
                BuildBudget = budget;
                BuildAfterArchive = Archives == 1;
            }
            return native.RunWithEnvironment(file, arguments, root, budget, environment);
        }
    }
}
