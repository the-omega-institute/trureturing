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
            modified[2] = modified[2].Replace("sys.exit(sys.modules['worktree_protocol'].main())", program, StringComparison.Ordinal);
            return production.Run(file, modified, directory, TimeSpan.FromSeconds(60));
        });
        var result = fixture.RunWithRaw(runner, force ? ["--force"] : []);
        Assert.True(injected);
        var failed = outcome is not ("eligible" or "refused");
        Assert.Equal(!failed, result.Success);
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
            Assert.Equal("deferred", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
        }
        else Assert.Equal("initialization_in_progress", reason);
        Assert.Contains(ReadItems(result.Output), item => ItemMatches(item, lane, failed ? "failed" : "skipped", reason));
    }

    public static IEnumerable<object[]> QualificationBoundaries()
    {
        foreach (var (stage, force) in new[] { ("batch", false), ("batch", true),
            ("preview", false), ("remove", true) })
            foreach (var failure in new[] { "outer_timeout", "traceback", "malformed", "missing" })
                yield return [stage, force, failure];
    }

    [Theory]
    [MemberData(nameof(QualificationBoundaries))]
    public void QualificationBoundaryRetainsFailureDiagnostic(string stage, bool force, string failure)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/boundary-failure");
        if (stage != "preview") fixture.LockLane(lane, "worktree-init:malformed");
        var runner = fixture.CreateRunner((file, args, _) =>
        {
            if (file != "python3" || !(stage == "batch" ? IsProtocol(args, "qualify")
                : IsProtocol(args, "remove") && args.Contains("--preview") == (stage == "preview"))) return null;
            if (failure == "outer_timeout") throw new TimeoutException("outer qualification deadline");
            return failure == "traceback"
                ? new ProcessOutput(17, [], Encoding.UTF8.GetBytes("Traceback (most recent call last):\n" + new string('x', 6000) + "\nOSError: causal qualification diagnostic\n"))
                : new ProcessOutput(0, Encoding.UTF8.GetBytes(failure == "missing"
                    ? "{\"event\":\"worktree_qualification\",\"status\":\"succeeded\",\"items\":[]}" : "{bad receipt"), []);
        });
        var result = fixture.RunWithRaw(runner, force ? ["--force"] : []);
        Assert.False(result.Success);
        Assert.True(Directory.Exists(lane));
        var reason = ReasonFor(result.Output, lane);
        Assert.StartsWith("qualification_failed:", reason);
        if (failure == "traceback") Assert.Contains("OSError: causal qualification diagnostic", reason);
        Assert.True(reason.Length < 10000);
        Assert.Contains(ReadItems(result.Output), item => ItemMatches(item, lane, "failed", reason));
        Assert.Equal(1, ReadSummary(result.Output).GetProperty("failed_count").GetInt32());
        Assert.Equal("deferred", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
    }
}
