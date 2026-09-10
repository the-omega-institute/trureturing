using System.Text.Json;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class RemoveWorktreesCommandTests
{
    [Fact]
    public void MissingNamesReturnsUsage64WithoutCallingGit()
    {
        var runner = new InventoryRunner();
        AssertResult(Run(runner), 64, 0, 0, 0);
        Assert.Empty(runner.Invocations);
    }

    [Fact]
    public void EmptyNamesReturnsUsage64WithoutCallingGit()
    {
        var runner = new InventoryRunner();
        AssertResult(Remove(runner, ""), 64, 0, 0, 0);
        Assert.Empty(runner.Invocations);
    }

    [Fact]
    public void WhitespaceNamesReturnsUsage64WithoutCallingGit()
    {
        var runner = new InventoryRunner();
        AssertResult(Remove(runner, " \t\r\n "), 64, 0, 0, 0);
        Assert.Empty(runner.Invocations);
    }

    [Theory]
    [InlineData("--names")]
    [InlineData("--name", "linked")]
    [InlineData("--names", "linked", "--force")]
    [InlineData("--names", "linked", "--names", "linked")]
    public void MalformedArgumentsReturnUsage64(params string[] arguments)
    {
        var runner = new InventoryRunner();
        AssertResult(Run(runner, arguments), 64, 0, 0, 0);
        Assert.Empty(runner.Invocations);
    }

    [Fact]
    public void UnregisteredNameReturnsNotFound65WithoutDeletion()
    {
        var runner = new InventoryRunner();
        var result = Remove(runner, "missing");
        AssertResult(result, 65, 0, 0, 1);
        AssertItem(result, "missing", null, "not_found");
        Assert.Empty(runner.Removals);
    }

    [Fact]
    public void DuplicateBasenamesReturnAmbiguous66WithoutDeletion()
    {
        var runner = new InventoryRunner(Entry("/fixture/main"), Entry("/one/same"), Entry("/two/same"));
        var result = Remove(runner, "same");
        Assert.Empty(runner.Removals);
        AssertResult(result, 66, 0, 0, 1);
        AssertItem(result, "same", null, "ambiguous");
        Assert.Contains("/one/same", result.Output, StringComparison.Ordinal);
        Assert.Contains("/two/same", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void MainWorktreeReturns67WithoutDeletion()
    {
        var runner = new InventoryRunner();
        var result = Remove(runner, "main");
        Assert.Empty(runner.Removals);
        AssertResult(result, 67, 0, 0, 1);
        AssertItem(result, "main", "/fixture/main", "main_worktree");
    }

    [Fact]
    public void MainWorktreeParticipatesInAmbiguityCount()
    {
        var runner = new InventoryRunner(Entry("/fixture/same"), Entry("/linked/same"));
        AssertResult(Remove(runner, "same"), 66, 0, 0, 1);
        Assert.Empty(runner.Removals);
    }

    [Fact]
    public void LockedWorktreeReturns68BeforeDeletingAnything()
    {
        var runner = new InventoryRunner(Entry("/fixture/main"), Entry("/fixture/locked", locked: true));
        var result = Remove(runner, "locked");
        AssertResult(result, 68, 0, 0, 1);
        AssertItem(result, "locked", "/fixture/locked", "locked");
        Assert.Contains("git worktree unlock", result.Output, StringComparison.Ordinal);
        Assert.Empty(runner.Removals);
    }

    [Fact]
    public void InventoryReadFailureReturns69WithoutDeletion()
    {
        var runner = new InventoryRunner { InventoryFailure = "fatal: inventory unavailable\n" };
        var result = Remove(runner, "linked");
        AssertResult(result, 69, 0, 0, 1);
        Assert.Contains("inventory unavailable", result.Output, StringComparison.Ordinal);
        Assert.Empty(runner.Removals);
    }

    [Fact]
    public void EmptyInventoryReturns69WithoutDeletion()
    {
        var runner = new InventoryRunner { Inventory = "" };
        AssertResult(Remove(runner, "linked"), 69, 0, 0, 1);
        Assert.Empty(runner.Removals);
    }

    [Fact]
    public void MalformedInventoryReturns69WithoutDeletion()
    {
        var runner = new InventoryRunner { Inventory = "worktree /fixture/main\0\0" };
        AssertResult(Remove(runner, "linked"), 69, 0, 0, 1);
        Assert.Empty(runner.Removals);
    }

    [Fact]
    public void MixedValidAndInvalidBatchMakesZeroRemovalCalls()
    {
        var runner = new InventoryRunner();
        var result = Remove(runner, "linked missing");
        Assert.Empty(runner.Removals);
        AssertResult(result, 65, 0, 0, 2);
        AssertItem(result, "linked", "/fixture/linked", "batch_refused");
        AssertItem(result, "missing", null, "not_found");
    }

    [Theory]
    [InlineData("linked locked missing same main", 68)]
    [InlineData("linked missing same main locked", 65)]
    [InlineData("linked same main locked missing", 66)]
    [InlineData("linked main locked missing same", 67)]
    public void BatchReportsEveryRefusalAndReturnsFirstInInputOrder(string names, int expectedExit)
    {
        var runner = new InventoryRunner(Entry("/fixture/main"), Entry("/fixture/linked"),
            Entry("/fixture/locked", locked: true), Entry("/one/same"), Entry("/two/same"));
        var result = Remove(runner, names);
        AssertResult(result, expectedExit, 0, 0, 5);
        AssertItem(result, "linked", "/fixture/linked", "batch_refused");
        AssertItem(result, "locked", "/fixture/locked", "locked");
        AssertItem(result, "missing", null, "not_found");
        AssertItem(result, "same", null, "ambiguous");
        AssertItem(result, "main", "/fixture/main", "main_worktree");
        Assert.Empty(runner.Removals);
    }

    [Fact]
    public void ExecutionFailureReturns74AndContinuesWithRemainingResolvedPaths()
    {
        const string originalError = "fatal: cannot remove linked\n  original detail\n";
        var runner = new InventoryRunner(Entry("/fixture/main"), Entry("/fixture/linked"), Entry("/fixture/next"))
        {
            FailedRemovalPath = "/fixture/linked",
            RemovalError = originalError,
        };
        var result = Remove(runner, "linked next");
        AssertResult(result, 74, 1, 1, 0);
        AssertItem(result, "linked", "/fixture/linked", "failed");
        AssertItem(result, "next", "/fixture/next", "removed");
        using var failedItem = JsonDocument.Parse(result.Output.Split('\n')[0]);
        Assert.Equal(originalError, failedItem.RootElement.GetProperty("error").GetString());
        Assert.Equal(["/fixture/linked", "/fixture/next"], runner.Removals.Select(call => call.Arguments[^1]));
    }

    [Fact]
    public void ExecutionExceptionReturns74AndContinuesWithRemainingResolvedPaths()
    {
        var runner = new InventoryRunner(Entry("/fixture/main"), Entry("/fixture/linked"), Entry("/fixture/next"))
        {
            FailedRemovalPath = "/fixture/linked",
            ThrowOnRemoval = true,
        };
        AssertResult(Remove(runner, "linked next"), 74, 1, 1, 0);
        Assert.Equal(2, runner.Removals.Count());
    }

    [Fact]
    public void SingleNameIsRemovedWithOneForceAndMainWorkingDirectory()
    {
        var runner = new InventoryRunner();
        var result = Remove(runner, "linked");
        AssertResult(result, 0, 1, 0, 0);
        AssertItem(result, "linked", "/fixture/linked", "removed");
        var remove = Assert.Single(runner.Removals);
        Assert.Equal("/fixture/main", remove.WorkingDirectory);
        Assert.Equal(["worktree", "remove", "--force", "--", "/fixture/linked"], remove.Arguments);
    }

    [Fact]
    public void MultipleNamesUseOneInventoryAndPreserveInputOrder()
    {
        var runner = new InventoryRunner(Entry("/fixture/main"), Entry("/fixture/a"), Entry("/fixture/b"));
        var result = Remove(runner, " \tb\r\na  ");
        AssertResult(result, 0, 2, 0, 0);
        Assert.Equal(["/fixture/b", "/fixture/a"], runner.Removals.Select(call => call.Arguments[^1]));
        Assert.Single(runner.Invocations, call => call.Arguments.SequenceEqual(["worktree", "list", "--porcelain", "-z"]));
    }

    [Fact]
    public void RepeatedNameIsRemovedOnlyOnce()
    {
        var runner = new InventoryRunner();
        AssertResult(Remove(runner, "linked linked\tlinked"), 0, 1, 0, 0);
        Assert.Single(runner.Removals);
    }

    [Fact]
    public void RemovalNeverConsultsReclamationCriteriaOrDeletesRefs()
    {
        var runner = new InventoryRunner();
        AssertResult(Remove(runner, "linked"), 0, 1, 0, 0);
        Assert.Equal(2, runner.Invocations.Count);
        Assert.All(runner.Invocations, call =>
        {
            Assert.Equal("git", call.FileName);
            Assert.Equal("worktree", call.Arguments[0]);
            Assert.Contains(call.Arguments[1], new[] { "list", "remove" });
            Assert.DoesNotContain(call.Arguments, arg =>
                new[] { "status", "merge-base", "rev-list", "log", "gh", "lsof", "update-ref", "branch", "-D" }.Contains(arg));
        });
    }

    [Theory]
    [InlineData("foo")]
    [InlineData("TRURETURING-FOO")]
    [InlineData("unrelated-branch")]
    [InlineData("/fixture/trureturing-foo")]
    [InlineData("../trureturing-foo")]
    public void NameUsesOnlyOrdinalCompleteBasename(string name)
    {
        var runner = new InventoryRunner(Entry("/fixture/main"), Entry("/fixture/trureturing-foo", "unrelated-branch"));
        AssertResult(Remove(runner, name), 65, 0, 0, 1);
        Assert.Empty(runner.Removals);
    }

    [Fact]
    public void CustomDestinationDetachedAndBranchMismatchAreRemovedByDirectoryName()
    {
        using var fixture = new RemovalFixture();
        var custom = fixture.Add("custom-destination", "unrelated-branch");
        var detached = fixture.Add("detached-destination");
        var result = fixture.Remove("custom-destination detached-destination");
        AssertResult(result, 0, 2, 0, 0);
        Assert.False(Directory.Exists(custom));
        Assert.False(Directory.Exists(detached));
        Assert.True(fixture.BranchExists("unrelated-branch"));
    }

    [Fact]
    public void DirtyUnmergedNewWorktreeIsRemovedAndItsBranchRefSurvives()
    {
        using var fixture = new RemovalFixture();
        var path = fixture.Add("fresh-dirty", "unmerged-branch");
        var branchHead = fixture.CommitAndDirty(path);
        var mainHead = fixture.Git(fixture.Main, "rev-parse", "HEAD").Trim();
        Assert.NotEqual(mainHead, branchHead);
        AssertResult(fixture.Remove("fresh-dirty"), 0, 1, 0, 0);
        Assert.False(Directory.Exists(path));
        Assert.Equal(branchHead, fixture.Git(fixture.Main, "rev-parse", "refs/heads/unmerged-branch").Trim());
    }

    [Fact]
    public void CallerLinkedWorktreeCanBeRemovedFromMainCheckout()
    {
        using var fixture = new RemovalFixture();
        var path = fixture.Add("caller");
        var result = WorktreeCommand.Run(path, ["remove", "--names", "caller"], fixture.Runner);
        AssertResult(result, 0, 1, 0, 0);
        Assert.False(Directory.Exists(path));
        Assert.Equal(fixture.Main, Assert.Single(fixture.Runner.Invocations, IsRemoval).WorkingDirectory);
    }

    [Fact]
    public void CliReturnsClassifiedCodeAndLeavesUnregisteredDirectoryUntouched()
    {
        using var fixture = new RemovalFixture();
        var unregistered = fixture.UnregisteredDirectory("not-registered");
        var console = new BufferedConsole();
        var exit = CliApplication.Run(["worktree", "remove", "--names", "not-registered"],
            new ProductionCliEnvironment(fixture.Main), console);
        Assert.Equal(65, exit);
        Assert.True(Directory.Exists(unregistered));
        Assert.EndsWith("WORKTREE_REMOVE_RESULT exit=65 removed=0 failed=0 refused=1\n", console.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void LockedSyntheticWorktreeRefusesWholeBatchUntilExplicitlyUnlocked()
    {
        using var fixture = new RemovalFixture();
        var open = fixture.Add("open");
        var locked = fixture.Add("locked");
        fixture.Git(fixture.Main, "worktree", "lock", "--reason", "fixture", locked);
        AssertResult(fixture.Remove("open locked"), 68, 0, 0, 2);
        Assert.DoesNotContain(fixture.Runner.Invocations, IsRemoval);
        Assert.True(Directory.Exists(open));
        Assert.True(Directory.Exists(locked));
        fixture.Git(fixture.Main, "worktree", "unlock", locked);
        AssertResult(fixture.Remove("open locked"), 0, 2, 0, 0);
    }

    [Fact]
    public void HelpDescribesRemovalNameLockForceAndTwoExitLayers()
    {
        var result = Run(new InventoryRunner(), "--help");
        Assert.True(result.Success, result.Error);
        foreach (var text in new[] { "--names", "complete", "whitespace", "unmerged", "dirty", "age", "open PR", "process", "git worktree unlock", "0/2", "WORKTREE_REMOVE_RESULT" })
            Assert.Contains(text, result.Output, StringComparison.Ordinal);
        Assert.Contains("StrataLint worktree remove --names", WorktreeCommand.Usage, StringComparison.Ordinal);
    }

    private static CommandResult Run(InventoryRunner runner, params string[] arguments) =>
        WorktreeCommand.Run("/fixture/linked", new[] { "remove" }.Concat(arguments).ToArray(), runner);

    private static CommandResult Remove(InventoryRunner runner, string names) => Run(runner, "--names", names);

    private static void AssertResult(CommandResult result, int exit, int removed, int failed, int refused)
    {
        Assert.Equal(exit, result.ExitCode);
        Assert.Equal(exit == 0, result.Success);
        Assert.EndsWith($"WORKTREE_REMOVE_RESULT exit={exit} removed={removed} failed={failed} refused={refused}\n",
            result.Output, StringComparison.Ordinal);
    }

    private static void AssertItem(CommandResult result, string name, string? path, string outcome)
    {
        var records = result.Output.Split('\n').Where(line => line.StartsWith('{'))
            .Select(line => JsonSerializer.Deserialize<Dictionary<string, JsonElement>>(line)!).ToArray();
        var item = Assert.Single(records, record => record["name"].GetString() == name);
        Assert.Equal(path, item["path"].GetString());
        Assert.Equal(outcome, item["outcome"].GetString());
    }
}
