using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void BranchDeletedAfterEnumerationIsSkippedAndScanContinues()
    {
        using var fixture = new CleanLanesFixture();
        const string vanished = "harness/race-a-vanished";
        const string control = "harness/race-z-control";
        fixture.AddOrphan(vanished, merged: true);
        fixture.AddOrphan(control, merged: true);
        var production = new ProductionWorktreeProcessRunner();
        var runner = fixture.CreateRunner((fileName, arguments, workingDirectory) =>
        {
            if (fileName != "git" || arguments.FirstOrDefault() != "for-each-ref") return null;

            var listing = production.Run(
                fileName,
                arguments,
                workingDirectory,
                BoundedProcessRunner.HangDetectionBudget);
            var deletion = production.Run(
                "git",
                ["update-ref", "-d", $"refs/heads/{vanished}"],
                workingDirectory,
                BoundedProcessRunner.HangDetectionBudget);
            Assert.Equal(0, deletion.ExitCode);
            return listing;
        });

        var result = fixture.RunWithRaw(runner, "--force");

        Assert.True(result.Success, result.Error);
        AssertItemProperty(ReadItems(result.Output), "branch", vanished, "reason", "vanished");
        AssertItemProperty(ReadItems(result.Output), "branch", control, "action", "removed");
        Assert.False(fixture.BranchExists(control));
    }

    [Fact]
    public void BranchResolutionFailureOtherThanMissingRefStillFailsClosed()
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/race-corrupt";
        fixture.AddOrphan(branch, merged: true);
        var runner = fixture.CreateRunner((fileName, arguments, _) =>
            fileName == "git"
            && arguments.FirstOrDefault() == "rev-parse"
            && arguments.Any(argument => argument.StartsWith($"refs/heads/{branch}", StringComparison.Ordinal))
                ? new ProcessOutput(128, [], Encoding.UTF8.GetBytes("fatal: bad object\n"))
                : null);

        var result = fixture.RunWithRaw(runner, "--force");

        Assert.False(result.Success);
        Assert.Contains("CLEAN_LANES_FAILED fatal: bad object", result.Error, StringComparison.Ordinal);
        Assert.True(fixture.BranchExists(branch));
    }
}
