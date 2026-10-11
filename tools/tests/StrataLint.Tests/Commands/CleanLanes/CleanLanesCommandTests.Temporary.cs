using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData(false, false, false)]
    [InlineData(false, true, false)]
    [InlineData(false, true, true)]
    [InlineData(true, false, false)]
    [InlineData(true, true, false)]
    [InlineData(true, true, true)]
    public void TemporarySweepUsesIndependentShapePolicy(bool pointer, bool force, bool lanesOnly)
    {
        using var fixture = new CleanLanesFixture();
        var path = pointer
            ? fixture.AddOrphanTempDirectory("trureturing-unregistered")
            : fixture.AddGitlessJudgeSnapshot("trureturing-gitless");
        // Neither remote publication nor byte equality is part of this sweep.
        File.WriteAllText(Path.Combine(path, "unpublished.txt"), "local temporary output\n");
        CleanLanesFixture.Git(fixture.RepositoryRoot, "remote", "remove", "origin");
        var arguments = new List<string> { "--base", "dev" };
        if (force) arguments.Add("--force");
        if (lanesOnly) arguments.Add("--lanes-only");

        var result = CleanLanesCommand.Run(fixture.RepositoryRoot, arguments,
            new ProductionWorktreeProcessRunner(), [Path.GetDirectoryName(path)!], new DateTimeOffset(2030, 1, 2, 0, 0, 0, TimeSpan.Zero));

        Assert.True(result.Success, result.Error);
        Assert.Equal(!force || lanesOnly, Directory.Exists(path));
        if (lanesOnly)
            Assert.DoesNotContain(ReadItems(result.Output), item => item.GetProperty("kind").GetString() == "temp_judge");
        else
            Assert.Contains(ReadItems(result.Output), item => ItemMatches(item, path,
                force ? "removed" : "would_remove",
                pointer ? "unregistered_same_repository" : "gitless_judge_snapshot"));
    }

    [Fact]
    public void TemporarySweepPreservesForeignNestedRegisteredAndLinkedTargets()
    {
        using var fixture = new CleanLanesFixture();
        var foreign = fixture.AddForeignTempDirectory("trureturing-foreign");
        fixture.AddGitlessJudgeSnapshot("trureturing-foreign");
        var reports = fixture.AddReportDirectory("trureturing-reports");
        var parent = fixture.AddGitlessJudgeSnapshot("trureturing-parent");
        var nested = fixture.AddNestedWorktree(parent);
        var registered = fixture.AddDetachedJudge("trureturing-registered");
        fixture.AddGitlessJudgeSnapshot("trureturing-registered");
        var alias = Path.Combine(Path.GetDirectoryName(parent)!, "trureturing-alias");
        Directory.CreateSymbolicLink(alias, foreign);
        var pointer = fixture.AddOrphanTempDirectory("trureturing-foreign-pointer");
        File.WriteAllText(Path.Combine(pointer, ".git"), $"gitdir: {Path.Combine(foreign, ".git")}\n");

        var result = fixture.RunWithProductionProbes(new ProductionWorktreeProcessRunner(), "--force");

        Assert.True(result.Success, result.Error);
        foreach (var path in new[] { foreign, reports, parent, nested, registered, alias, pointer, fixture.RepositoryRoot })
            Assert.True(Directory.Exists(path), path);
        Assert.Equal("foreign_git_directory", ReasonFor(result.Output, foreign));
        Assert.Equal("foreign_git_directory", ReasonFor(result.Output, pointer));
        Assert.Equal("not_judge_tree", ReasonFor(result.Output, reports));
        Assert.Equal("nested_worktree", ReasonFor(result.Output, parent));
        Assert.Equal("symlink", ReasonFor(result.Output, alias));
        Assert.Equal("not_far_behind", ReasonFor(result.Output, registered));
        Assert.Equal("main_worktree", ReasonFor(result.Output, fixture.RepositoryRoot));
    }

    [Fact]
    public void TemporarySweepReportsDeleteFailureAndContinues()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new CleanLanesFixture();
        var denied = fixture.AddGitlessJudgeSnapshot("trureturing-a-denied");
        var healthy = fixture.AddOrphanTempDirectory("trureturing-z-healthy");
        var directory = Path.Combine(denied, "D5");
        File.WriteAllText(Path.Combine(directory, "output"), "temporary\n");
        var original = File.GetUnixFileMode(directory);
        File.SetUnixFileMode(directory, UnixFileMode.UserRead | UnixFileMode.UserExecute);
        try
        {
            var result = fixture.RunWithProductionProbes(new ProductionWorktreeProcessRunner(), "--force");
            Assert.False(result.Success);
            Assert.Equal("CLEAN_LANES_PARTIAL_FAILURE count=1\n", result.Error);
            Assert.True(Directory.Exists(denied));
            Assert.False(Directory.Exists(healthy));
            Assert.Equal("temporary_directory_partial_or_indeterminate", ReasonFor(result.Output, denied));
            Assert.Equal("unregistered_same_repository", ReasonFor(result.Output, healthy));
            Assert.Equal(1, ReadSummary(result.Output).GetProperty("partial_count").GetInt32());
            Assert.Equal(1, ReadSummary(result.Output).GetProperty("removed_count").GetInt32());
        }
        finally
        {
            File.SetUnixFileMode(directory, original);
        }
    }
}
