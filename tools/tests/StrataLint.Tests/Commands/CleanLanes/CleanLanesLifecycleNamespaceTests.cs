using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    private static string ExpectedCreationNamespace => WorktreeCommand.CreationNamespace;
    private static string HistoricalLifecycleNamespace =>
        WorktreeCommand.HistoricalLifecycleNamespace;

    [Fact]
    public void CurrentNamespaceRegisteredLaneIsInLifecycleCleanup()
    {
        using var fixture = new CleanLanesFixture();
        var branch = $"{ExpectedCreationNamespace}/registered";
        var path = fixture.AddLandedLane(branch);

        var result = fixture.Run();

        Assert.True(result.Success, result.Error);
        AssertItemProperty(ReadItems(result.Output), "path", path, "action", "would_remove");
    }

    [Fact]
    public void HistoricalNamespaceRegisteredLaneRemainsInLifecycleCleanup()
    {
        using var fixture = new CleanLanesFixture();
        var branch = $"{HistoricalLifecycleNamespace}/registered";
        var path = fixture.AddLandedLane(branch);

        var result = fixture.Run();

        Assert.True(result.Success, result.Error);
        AssertItemProperty(ReadItems(result.Output), "path", path, "action", "would_remove");
    }

    [Fact]
    public void WorktreesOutsideLifecycleNamespacesAreReclaimedWithoutDeletingTheirBranches()
    {
        using var fixture = new CleanLanesFixture();
        const string registeredBranch = "feature/registered";
        const string orphanBranch = "feature/orphan";
        var registeredPath = fixture.AddLandedLane(registeredBranch);
        fixture.AddOrphan(orphanBranch, merged: true);

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(registeredPath));
        Assert.True(fixture.BranchExists(registeredBranch));
        Assert.True(fixture.BranchExists(orphanBranch));
        Assert.DoesNotContain(
            ReadItems(result.Output),
            item => item.TryGetProperty("branch", out var branch)
                && branch.GetString() == orphanBranch);
    }

}
