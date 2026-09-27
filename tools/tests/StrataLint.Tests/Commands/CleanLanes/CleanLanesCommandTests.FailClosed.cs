using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void ForceRetainsLaneAndContinuesWhenRefreshedInventoryOmitsIt()
    {
        using var fixture = new CleanLanesFixture();
        var retained = fixture.AddLandedLane("harness/refresh-omitted-a-retained");
        var removed = fixture.AddLandedLane("harness/refresh-omitted-z-control");
        var inventoryCalls = 0;
        var production = new ProductionWorktreeProcessRunner();
        var runner = fixture.CreateRunner((fileName, arguments, workingDirectory) =>
        {
            if (fileName != "git"
                || !arguments.SequenceEqual(["worktree", "list", "--porcelain", "-z"]))
            {
                return null;
            }

            inventoryCalls++;
            if (inventoryCalls != 2) return null;

            var output = production.Run(
                fileName,
                arguments,
                workingDirectory,
                BoundedProcessRunner.HangDetectionBudget);
            var inventory = Encoding.UTF8.GetString(output.StandardOutput);
            var recordStart = inventory.IndexOf(
                $"worktree {retained}\0",
                StringComparison.Ordinal);
            var nextRecord = inventory.IndexOf(
                "worktree ",
                recordStart + 1,
                StringComparison.Ordinal);
            Assert.True(recordStart >= 0);
            var withoutRetained = inventory.Remove(
                recordStart,
                (nextRecord < 0 ? inventory.Length : nextRecord) - recordStart);

            return new ProcessOutput(
                output.ExitCode,
                Encoding.UTF8.GetBytes(withoutRetained),
                output.StandardError);
        });

        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");

        Assert.Equal(3, inventoryCalls);
        AssertRetainedAndControlReclaimed(result, retained, removed, "unreadable");
    }
}
