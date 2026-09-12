using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class LeanCacheProvisionerTests
{
    [Theory]
    [InlineData("timeout", true, 1)]
    [InlineData("nonzero", true, 1)]
    [InlineData("materialization", false, 0)]
    [InlineData("pins", false, 0)]
    [InlineData("build", false, 1)]
    public void OptionalFetchFailureStillReachesLocalBuild(string fault, bool success, int builds)
    {
        using var fixture = new SharedLakeFixture(native: true);
        var root = fixture.Main;
        var dependency = Path.Combine(root, "mathlib");
        Directory.CreateDirectory(dependency);
        File.WriteAllText(Path.Combine(dependency, "lakefile.toml"), "name = \"mathlib\"\n");
        File.AppendAllText(Path.Combine(root, "lakefile.toml"),
            "\n[[require]]\nname = \"mathlib\"\npath = \"mathlib\"\n");
        var updated = TestProcessRunner.Run(fixture.Lake, ["update"], root,
            TestBudgets.LeanProcessHangGuard, 1024 * 1024);
        Assert.Equal(0, updated.ExitCode);
        var prior = Path.Combine(root, ".lake", "build", "prior.olean");
        Directory.CreateDirectory(Path.GetDirectoryName(prior)!);
        File.WriteAllText(prior, "private output retained");
        if (fault == "pins") File.Delete(Path.Combine(root, "lean-toolchain"));
        if (fault == "build") File.WriteAllText(Path.Combine(root, "Fixture.lean"), "unknown_command\n");
        var runner = new FetchFaultRunner(fault);
        var result = WorktreeCommand.Run(root, ["with-cache-reader", "--", "lake", "build"], runner);
        Assert.True(result.Success == success, result.Output + result.Error);
        Assert.Equal(builds, runner.Builds);
        Assert.Equal("private output retained", File.ReadAllText(prior));
        if (fault is "timeout" or "nonzero")
        {
            Assert.Contains("\"status\":\"degraded\"", result.Output);
            Assert.Contains("injected " + fault, result.Output);
            Assert.True(File.Exists(Path.Combine(root, ".lake", "build", "lib", "lean", "Fixture.olean")));
            Assert.False(File.Exists(LeanCacheStamp.PathFor(Path.Combine(root, ".lake"))));
        }
        if (fault == "build") Assert.Equal(1, result.ExitCode);
    }

    private sealed class FetchFaultRunner(string fault) : IWorktreeProcessRunner
    {
        private readonly ProductionWorktreeProcessRunner native = new();
        internal int Builds { get; private set; }
        public ProcessOutput Run(string file, IReadOnlyList<string> args, string root, TimeSpan budget) =>
            native.Run(file, args, root, budget);

        public ProcessOutput RunWithEnvironment(string file, IReadOnlyList<string> args, string root,
            TimeSpan budget, IReadOnlyDictionary<string, string> environment)
        {
            var target = file;
            var targetArgs = args;
            if (target == "/usr/bin/perl")
            {
                var index = 3 + int.Parse(targetArgs[2], System.Globalization.CultureInfo.InvariantCulture);
                target = targetArgs[index];
                targetArgs = targetArgs.Skip(index + 1).ToArray();
            }
            if (target == "/usr/bin/sandbox-exec") targetArgs = targetArgs.Skip(3).ToArray();
            if (targetArgs.SequenceEqual(new[] { "exe", "cache", "get" }))
            {
                if (fault == "timeout") throw new TimeoutException("injected timeout");
                return new(1, [], Encoding.UTF8.GetBytes("injected nonzero"));
            }
            if (fault == "materialization" && targetArgs.FirstOrDefault() == "env")
                return new(1, [], Encoding.UTF8.GetBytes("injected materialization failure"));
            if (targetArgs.FirstOrDefault() == "build") Builds++;
            return native.RunWithEnvironment(file, args, root, budget, environment);
        }
    }
}
