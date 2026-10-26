using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void InitializationSelectionPreservesCanonicalQualificationRefusal(bool force)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/canonical-initialization-refusal");
        fixture.LockLane(lane, "worktree-init:malformed");
        var qualified = 0;
        var production = new ProductionWorktreeProcessRunner();
        var runner = fixture.CreateRunner((file, args, directory) =>
        {
            if (file != "python3" || !IsQualification(args)) return null;
            qualified++;
            var modified = args.ToArray();
            modified[2] = modified[2].Replace("sys.exit(sys.modules['worktree_protocol'].main())", """
                def refuse(*args, **kwargs):
                    raise sys.modules['worktree_protocol'].Refused('initialization_in_progress')
                sys.modules['worktree_preservation'].qualify = refuse
                sys.exit(sys.modules['worktree_protocol'].main())
                """, StringComparison.Ordinal);
            return production.Run(file, modified, directory, TimeSpan.FromSeconds(60));
        });

        var result = fixture.RunWithRaw(runner, force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

        Assert.True(result.Success, result.Error);
        Assert.Equal("initialization_in_progress", ReasonFor(result.Output, lane));
        Assert.Equal(1, qualified);
        Assert.True(Directory.Exists(lane));
    }

    [Fact]
    public void InitializationSelectionUsesCanonicalLivenessAndRemovalRequalifies()
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/canonical-initialization-liveness";
        var lane = fixture.AddLandedLane(branch);
        fixture.LockLane(lane, "worktree-init:malformed");
        using var entry = WorktreeInitializationScope.AcquireTree(lane, lane);
        var qualified = 0;
        var production = new ProductionWorktreeProcessRunner();
        var runner = fixture.CreateRunner((file, args, directory) =>
        {
            if (file != "python3" || !IsQualification(args)) return null;
            qualified++;
            var modified = args.ToArray();
            modified[2] = modified[2].Replace("sys.exit(sys.modules['worktree_protocol'].main())", """
                sys.modules['worktree_preservation'].tree_scope = lambda *args, **kwargs: None
                sys.exit(sys.modules['worktree_protocol'].main())
                """, StringComparison.Ordinal);
            return production.Run(file, modified, directory, TimeSpan.FromSeconds(60));
        });

        var preview = fixture.RunWithRaw(runner, "--lanes-only");
        Assert.True(preview.Success, preview.Error);
        Assert.Contains(ReadItems(preview.Output), item => ItemMatches(item, lane, "would_remove", "merged_to_dev"));
        Assert.True(qualified > 0);
        var removal = fixture.RunWithRaw(runner, "--force", "--lanes-only");
        Assert.True(removal.Success, removal.Error);
        Assert.Equal("initialization_in_progress", ReasonFor(removal.Output, lane));
        Assert.True(Directory.Exists(lane));
    }

    [Fact]
    public void InitializationLivenessDoesNotMistakeBusyRefForTreeEntry()
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/initialization-ref-busy";
        var lane = fixture.AddLandedLane(branch);
        fixture.LockLane(lane, "worktree-init:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
        using var reference = WorktreeInitializationScope.AcquireReference(lane, branch);
        var preview = fixture.Run("--lanes-only");
        Assert.Contains(ReadItems(preview.Output), item => ItemMatches(item, lane, "would_remove", "merged_to_dev"));
        var removal = fixture.Run("--force", "--lanes-only");
        Assert.StartsWith("checkpoint_failed:busy_scope:ref:", ReasonFor(removal.Output, lane));
        Assert.True(Directory.Exists(lane));
    }

    [Fact]
    public void CurrentInitializationMarkerUsesExclusiveScopeLiveness()
    {
        using var fixture = new CleanLanesFixture();
        var branch = "harness/current-initialization";
        var lane = fixture.AddLandedLane(branch);
        fixture.LockLane(lane, "worktree-init:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
        File.SetLastWriteTimeUtc(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked"),
            new DateTime(2030, 1, 2, 0, 0, 0, DateTimeKind.Utc));
        using (WorktreeInitializationScope.Acquire(lane, lane, branch))
        {
            var alive = fixture.Run("--force", "--lanes-only");
            Assert.Equal("initialization_in_progress", ReasonFor(alive.Output, lane));
            Assert.True(Directory.Exists(lane));
        }
        var dead = fixture.Run("--force", "--lanes-only");
        Assert.True(dead.Success, dead.Error);
        Assert.False(Directory.Exists(lane), dead.Output);
    }

    [Theory]
    [InlineData("manual")]
    [InlineData("worktree-init:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa")]
    [InlineData("worktree-init:malformed")]
    [InlineData("")]
    public void ElapsedLocksUseTheSameRemovalPolicy(string reason)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/elapsed-lock");
        fixture.LockLane(lane, reason);
        var preview = fixture.Run("--lanes-only");
        Assert.True(preview.Success, preview.Error);
        Assert.Contains(ReadItems(preview.Output), item => ItemMatches(item, lane, "would_remove", "merged_to_dev"));
        Assert.True(Directory.Exists(lane));
        var result = fixture.Run("--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane), result.Output);
    }

    [Fact]
    public void CurrentLockIsRetainedByAutomaticSelection()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/current-lock");
        fixture.LockLane(lane);
        File.SetLastWriteTimeUtc(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked"),
            new DateTime(2030, 1, 2, 0, 0, 0, DateTimeKind.Utc));
        var result = fixture.Run("--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.Equal("locked_recent", ReasonFor(result.Output, lane));
        Assert.True(Directory.Exists(lane));
    }
}
