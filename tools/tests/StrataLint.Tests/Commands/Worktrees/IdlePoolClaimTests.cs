using System.Text.Json;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class WorktreeCommandTests
{
    [Fact]
    public void IdlePoolBypassesAutomaticAgeButAllowsNamedRemoval()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        TestGit.Run(repository.Path, "update-ref", "refs/remotes/origin/dev", "HEAD");
        var idle = Path.Combine(repository.Path, "idle");
        var token = Guid.NewGuid().ToString("N");
        var idleBranch = "refs/heads/lane/governance/idle-" + token;
        TestGit.Run(repository.Path, "update-ref", "--create-reflog", "-m", "worktree-idle:" + token,
            idleBranch, "HEAD");
        TestGit.Run(repository.Path, "worktree", "add", idle, idleBranch["refs/heads/".Length..]);

        var result = CleanLanesCommand.Run(repository.Path, ["--force", "--lanes-only"],
            new DateTimeOffset(2030, 1, 2, 0, 0, 0, TestBudgets.ZeroDuration));

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(idle));
        Assert.Contains("idle_pool", result.Output, StringComparison.Ordinal);
        var removed = WorktreeCommand.Run(repository.Path, ["remove", "--names", "idle"]);
        Assert.True(removed.Success, removed.Error);
        Assert.False(Directory.Exists(idle));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void IdleClaimUsesActualPathAndKeepsTaskBranchAndCache(bool exact)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        TestGit.Run(repository.Path, "update-ref", "refs/remotes/origin/dev", "HEAD");
        var idle = Path.Combine(repository.Path, "idle");
        var token = Guid.NewGuid().ToString("N");
        var idleBranch = "refs/heads/lane/governance/idle-" + token;
        TestGit.Run(repository.Path, "update-ref", "--create-reflog", "-m", "worktree-idle:" + token,
            idleBranch, "HEAD");
        TestGit.Run(repository.Path, "worktree", "add", idle, idleBranch["refs/heads/".Length..]);
        TestGit.Run(repository.Path, "config", "core.excludesFile", Path.Combine(repository.Path, "ignore"));
        File.WriteAllText(Path.Combine(repository.Path, "ignore"), ".lake/\n");
        Directory.CreateDirectory(Path.Combine(idle, ".lake"));
        File.WriteAllText(Path.Combine(idle, ".lake", "sentinel"), "cached bytes\n");
        var fallback = Path.Combine(repository.Path, "fallback");
        var arguments = new List<string> { "--kind", "math", "--name", "claimed", "--base", "dev",
            "--path", exact ? idle : fallback, "--skip-restore" };
        if (!exact) arguments.Add("--prefer-idle");

        var result = WorktreeCommand.Run(repository.Path, arguments);

        Assert.True(result.Success, result.Error);
        using var receipt = JsonDocument.Parse(result.Output);
        Assert.Equal("claimed", receipt.RootElement.GetProperty("status").GetString());
        var registeredPath = WorktreeHookFixture.RunGit(idle, "rev-parse", "--show-toplevel").Trim();
        Assert.Contains("worktree " + registeredPath + "\n",
            WorktreeHookFixture.RunGit(repository.Path, "worktree", "list", "--porcelain"), StringComparison.Ordinal);
        Assert.Equal(registeredPath, receipt.RootElement.GetProperty("path").GetString());
        Assert.False(Directory.Exists(fallback));
        Assert.Equal("cached bytes\n", File.ReadAllText(Path.Combine(idle, ".lake", "sentinel")));
        Assert.Equal("lane/math/claimed", WorktreeHookFixture.RunGit(idle, "branch", "--show-current").Trim());
        Assert.Contains("worktree-allocation:", WorktreeHookFixture.RunGit(idle, "reflog", "-1", "--format=%gs"));
        var repeated = WorktreeCommand.Run(repository.Path, arguments);
        Assert.True(repeated.Success, repeated.Error);
        using var reuse = JsonDocument.Parse(repeated.Output);
        Assert.Equal("reused", reuse.RootElement.GetProperty("status").GetString());
        Assert.Equal(registeredPath, reuse.RootElement.GetProperty("path").GetString());
    }
}
