using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    public static IEnumerable<object[]> QualificationStages()
    {
        foreach (var (stage, force) in new[] { ("batch", false), ("batch", true),
            ("preview", false), ("preflight", true), ("scoped", true) })
            foreach (var outcome in new[] { "eligible", "refused", "git", "os", "inner_timeout" })
                yield return [stage, force, outcome];
    }

    [Theory]
    [MemberData(nameof(QualificationStages))]
    public void QualificationStagePreservesOutcomeAndCause(string stage, bool force, string outcome)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/stage-outcome");
        if (stage != "preview") fixture.LockLane(lane, "worktree-init:malformed");
        var production = new ProductionWorktreeProcessRunner();
        var injected = false;
        var runner = fixture.CreateRunner((file, args, directory) =>
        {
            if (file != "python3" || !(stage == "batch" ? IsProtocol(args, "qualify")
                : IsProtocol(args, "remove") && args.Contains("--preview") == (stage == "preview"))) return null;
            injected = true;
            var modified = args.ToArray();
            var failure = outcome switch
            {
                "git" => "raise p.GitFailure('fatal: native qualification broke')",
                "os" => "raise OSError('qualification filesystem broke')",
                "inner_timeout" => "raise subprocess.TimeoutExpired(['git'], 300, stderr=b'inner qualification deadline')",
                "refused" => "raise p.Refused('initialization_in_progress')",
                _ => "return original(*args, **kwargs)",
            };
            var program = $"""
                import subprocess
                p = sys.modules['worktree_protocol']
                preservation = sys.modules['worktree_preservation']
                original = preservation.qualify
                calls = 0
                def injected_qualification(*args, **kwargs):
                    global calls
                    calls += 1
                    if calls == {(stage == "scoped" ? 2 : 1)}:
                        {failure}
                    return original(*args, **kwargs)
                preservation.qualify = injected_qualification
                sys.exit(p.main())
                """;
            File.WriteAllText(modified[2], File.ReadAllText(modified[2]).Replace("sys.exit(sys.modules['worktree_protocol'].main())", program, StringComparison.Ordinal));
            return production.Run(file, modified, directory, TimeSpan.FromSeconds(60));
        });
        var result = fixture.RunWithRaw(runner, force ? ["--force"] : []);
        Assert.True(injected);
        var failed = outcome is not ("eligible" or "refused");
        Assert.True(result.Success, result.Error);
        AssertQualificationPublicExit(result, force, 0);
        Assert.Equal(failed ? 1 : 0, ReadSummary(result.Output).GetProperty("failed_count").GetInt32());
        if (outcome == "eligible")
        {
            Assert.Equal(!force, Directory.Exists(lane));
            Assert.Contains(ReadItems(result.Output), item => ItemMatches(item, lane,
                force ? "removed" : "would_remove", ReasonFor(result.Output, lane)));
            return;
        }
        Assert.True(Directory.Exists(lane));
        var reason = ReasonFor(result.Output, lane);
        if (failed)
        {
            Assert.StartsWith("qualification_failed:", reason);
            Assert.Contains(outcome switch { "git" => "native qualification broke", "os" => "filesystem broke",
                _ => "inner qualification deadline" }, reason);
            Assert.Equal("completed", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
        }
        else Assert.Equal("initialization_in_progress", reason);
        Assert.Contains(ReadItems(result.Output), item => ItemMatches(item, lane, failed ? "failed" : "skipped", reason));
        Assert.Equal(outcome == "refused" && stage == "batch" ? 0 : 1,
            ReadEvents(result.Error, "clean_lanes_warning").Count);
    }

    public static IEnumerable<object[]> QualificationBoundaries()
    {
        foreach (var (stage, force) in new[] { ("batch", false), ("batch", true),
            ("preview", false), ("remove", true) })
            foreach (var failure in new[] { "outer_timeout", "unavailable", "start_refused", "traceback", "malformed", "missing" })
                yield return [stage, force, failure];
    }

    [Theory]
    [MemberData(nameof(QualificationBoundaries))]
    public void QualificationBoundaryRetainsFailureDiagnostic(string stage, bool force, string failure)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/boundary-failure");
        if (stage != "preview") fixture.LockLane(lane, "worktree-init:malformed");
        var runner = fixture.CreateRunner((file, args, directory) =>
        {
            if (file != "python3" || !(stage == "batch" ? IsProtocol(args, "qualify")
                : IsProtocol(args, "remove") && args.Contains("--preview") == (stage == "preview"))) return null;
            if (failure == "outer_timeout") throw new TimeoutException("outer qualification deadline");
            if (failure is "unavailable" or "start_refused")
            {
                var previous = BoundedProcessRunner.StartProcess.Value;
                try
                {
                    BoundedProcessRunner.StartProcess.Value = _ => failure == "start_refused" ? false
                        : throw new System.ComponentModel.Win32Exception("python unavailable at qualification boundary");
                    return new ProductionWorktreeProcessRunner().Run(file, args, directory, TimeSpan.FromSeconds(600));
                }
                finally { BoundedProcessRunner.StartProcess.Value = previous; }
            }
            return failure == "traceback"
                ? new ProcessOutput(17, [], Encoding.UTF8.GetBytes("Traceback (most recent call last):\n" + new string('x', 6000) + "\nOSError: causal qualification diagnostic\n"))
                : new ProcessOutput(0, Encoding.UTF8.GetBytes(failure == "missing"
                    ? "{\"event\":\"worktree_qualification\",\"status\":\"succeeded\",\"items\":[]}" : "{bad receipt"), []);
        });
        var result = fixture.RunWithRaw(runner, force ? ["--force"] : []);
        Assert.True(result.Success, result.Error);
        AssertQualificationPublicExit(result, force, 0);
        Assert.True(Directory.Exists(lane));
        var reason = ReasonFor(result.Output, lane);
        var indeterminate = stage == "remove" && failure is not ("unavailable" or "start_refused");
        Assert.StartsWith(indeterminate ? "worktree_remove_failed_state_indeterminate" : "qualification_failed:", reason);
        var item = Assert.Single(ReadItems(result.Output), item => item.GetProperty("path").GetString() == lane);
        if (failure == "traceback") Assert.Contains("OSError: causal qualification diagnostic",
            indeterminate ? item.GetProperty("diagnostic").GetString() : reason);
        Assert.True(reason.Length < 10000);
        Assert.Equal(indeterminate ? "partially_removed" : "failed", item.GetProperty("action").GetString());
        Assert.Equal(indeterminate ? 0 : 1, ReadSummary(result.Output).GetProperty("failed_count").GetInt32());
        Assert.Equal(indeterminate ? 1 : 0, ReadSummary(result.Output).GetProperty("partial_count").GetInt32());
        Assert.Equal("completed", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
    }
    private static void AssertQualificationPublicExit(CommandResult result, bool force, int expected)
    {
        var console = new BufferedConsole();
        var environment = new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused"), cleanLanes: result);
        var exit = CliApplication.Run(force ? ["clean-lanes", "--force"] : ["clean-lanes"], environment, console);
        Assert.Equal(expected, exit);
        Assert.Equal(result.Output, console.Output);
        Assert.Equal(result.Error, console.Error);
    }

}
