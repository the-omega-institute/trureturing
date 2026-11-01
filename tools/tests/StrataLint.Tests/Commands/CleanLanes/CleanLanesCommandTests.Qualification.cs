using System.ComponentModel;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData(false, false)]
    [InlineData(true, false)]
    [InlineData(false, true)]
    [InlineData(true, true)]
    public void NestedQualificationFailureCannotBeHiddenByStructuralGuards(bool force, bool disappears)
    {
        using var fixture = new CleanLanesFixture();
        var parent = fixture.AddLandedLane("harness/failed-parent");
        var child = fixture.AddNestedWorktree(parent);
        CleanLanesFixture.Git(child, "commit", "--allow-empty", "-m", "retained nested work");
        fixture.LockLane(parent, "worktree-init:malformed");
        var runner = fixture.CreateRunner((file, args, _) =>
        {
            if (file != "python3" || !IsProtocol(args, "qualify")) return null;
            if (disappears) File.Delete(Path.Combine(parent, ".git"));
            throw new Win32Exception("nested qualification unavailable");
        });
        var result = fixture.RunWithRaw(runner, force ? ["--force"] : []);
        Assert.True(result.Success, result.Error);
        AssertQualificationPublicExit(result, force, 0);
        Assert.Equal(1, ReadSummary(result.Output).GetProperty("failed_count").GetInt32());
        Assert.Equal("completed", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
        Assert.Contains("nested qualification unavailable", ReasonFor(result.Output, parent));
        Assert.Contains(ReadItems(result.Output), item => ItemMatches(item, parent, "failed", ReasonFor(result.Output, parent)));
        Assert.True(Directory.Exists(parent));
        Assert.True(Directory.Exists(child));
    }

    [Theory]
    [InlineData(false, "timeout")]
    [InlineData(true, "timeout")]
    [InlineData(false, "unavailable")]
    [InlineData(true, "unavailable")]
    [InlineData(false, "exception")]
    [InlineData(true, "exception")]
    [InlineData(false, "abnormal_exit")]
    [InlineData(true, "abnormal_exit")]
    [InlineData(false, "noncanonical")]
    [InlineData(true, "noncanonical")]
    [InlineData(false, "invalid_success")]
    [InlineData(true, "invalid_success")]
    public void LockedQualificationFailureRetainsTreeAndWarns(bool force, string failure)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/qualification-failure");
        fixture.LockLane(lane, "worktree-init:malformed");
        var runner = fixture.CreateRunner((file, args, _) =>
        {
            if (file != "python3" || !IsQualification(args)) return null;
            return failure switch
            {
                "timeout" => throw new TimeoutException("qualification deadline expired"),
                "unavailable" => throw new Win32Exception("python executable unavailable"),
                "exception" => throw new InvalidOperationException("unexpected qualification error"),
                "abnormal_exit" => new ProcessOutput(17, [], Encoding.UTF8.GetBytes("python crashed\nsecond line\n")),
                "noncanonical" => new ProcessOutput(73, [], Encoding.UTF8.GetBytes("unexpected refusal output\n")),
                _ => new ProcessOutput(0, Encoding.UTF8.GetBytes("not a qualification receipt"), []),
            };
        });

        var result = fixture.RunWithRaw(runner, force ? ["--force"] : []);

        Assert.True(result.Success, result.Error);
        AssertQualificationPublicExit(result, force, 0);
        var reason = ReasonFor(result.Output, lane);
        Assert.StartsWith("qualification_failed:", reason);
        Assert.Contains(failure switch
        {
            "timeout" => "timeout:TimeoutException:qualification deadline expired",
            "unavailable" => "unavailable:Win32Exception:python executable unavailable",
            "exception" => "unavailable:InvalidOperationException:unexpected qualification error",
            "abnormal_exit" => "exit=17:stderr=python crashed",
            "noncanonical" => "exit=73:stderr=unexpected refusal output",
            _ => "not a qualification receipt",
        }, reason);
        Assert.Contains(ReadItems(result.Output), item => ItemMatches(item, lane, "failed", reason));
        Assert.Equal(1, ReadSummary(result.Output).GetProperty("failed_count").GetInt32());
        Assert.Equal("completed", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
        Assert.True(Directory.Exists(lane));
        Assert.DoesNotContain(runner.Invocations, call => IsProtocol(call.Arguments, "remove")
            && !call.Arguments.Contains("--preview"));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void LockedQualificationBatchesCandidatesAndPreservesPerTreeReasons(bool force)
    {
        using var fixture = new CleanLanesFixture();
        var recent = fixture.AddLandedLane("harness/batch-recent");
        var abandoned = fixture.AddLandedLane("harness/batch-abandoned");
        fixture.LockLane(recent);
        File.SetLastWriteTimeUtc(Path.Combine(fixture.WorktreeGitDirectory(recent), "locked"),
            new DateTime(2030, 1, 2, 0, 0, 0, DateTimeKind.Utc));
        fixture.LockLane(abandoned, "worktree-init:malformed");
        var runner = fixture.CreateRunner();

        var result = fixture.RunWithRaw(runner, force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

        Assert.True(result.Success, result.Error);
        Assert.Equal("locked_recent", ReasonFor(result.Output, recent));
        Assert.True(Directory.Exists(recent));
        Assert.Equal(!force, Directory.Exists(abandoned));
        var qualification = Assert.Single(runner.Invocations, call => IsQualification(call.Arguments));
        Assert.Contains(recent, qualification.Arguments);
        Assert.Contains(abandoned, qualification.Arguments);
    }

    private static bool IsQualification(IReadOnlyList<string> args) =>
        IsProtocol(args, "qualify") || IsProtocol(args, "remove") && args.Contains("--preview");
}
