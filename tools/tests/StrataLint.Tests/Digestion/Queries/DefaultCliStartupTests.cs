using System.Text;
using System.Text.Json;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class DefaultCliStartupTests
{
    [Fact]
    public void DefaultCliValidatesBranchOutsideRepositoryWithoutScribeInputs()
    {
        using var temporary = new TemporaryDirectory();
        var branch = $"{WorktreeCommand.CreationNamespace}/{WorktreeCommand.CreationKinds[0]}/startup";

        var result = RunCli(temporary.Path, "worktree", "validate-branch", "--branch", branch);

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        using var receipt = JsonDocument.Parse(result.StandardOutput);
        Assert.Equal("branch_validation", receipt.RootElement.GetProperty("event").GetString());
        Assert.Equal(branch, receipt.RootElement.GetProperty("branch").GetString());
        Assert.True(receipt.RootElement.GetProperty("canonical").GetBoolean());
    }

    [Fact]
    public void DefaultCliBulkCandidatesNeedNoLeanReportOrScribeDiscoveryFixtures()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        foreach (var (path, content) in fixture.Files)
        {
            var destination = Path.Combine(temporary.Path, path);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            TemporaryFileSystem.File.WriteAllText(destination, content);
        }
        ReviewRegressionTests.RunGit(temporary.Path, "init");
        ReviewRegressionTests.RunGit(temporary.Path, "add", ".");
        ReviewRegressionTests.RunGit(temporary.Path, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.test",
            "commit", "-m", "synthetic query baseline");

        var result = RunCli(temporary.Path, "digest-status", "--formalize-candidates");

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        using var candidates = JsonDocument.Parse(result.StandardOutput);
        Assert.Equal("stratalint-formalize-candidates-v5", candidates.RootElement.GetProperty("schema").GetString());
    }

    private static StrataLint.Engine.ProcessOutput RunCli(string root, params string[] arguments) =>
        TestProcessRunner.Run(Path.Combine(AppContext.BaseDirectory, "StrataLint"), arguments, root,
            TestBudgets.LocalProcessHangGuard, 1024 * 1024);
}
