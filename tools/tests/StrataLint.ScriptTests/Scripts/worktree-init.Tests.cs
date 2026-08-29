namespace StrataLint.ScriptTests;

[ScriptSubject("tools/scripts/worktree-init.sh")]
public sealed partial class WorktreeInitScriptTests
{
    private const string WorktreeInitScriptPath = "tools/scripts/worktree-init.sh";

    [Fact]
    public void WorktreeAdapterPreservesTheCallerToolPathAndResolvesTheRepositoryRoot()
    {
        var script = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/scripts/worktree-init.sh"));
        var dirnameIndex = script.IndexOf("dirname", StringComparison.Ordinal);
        var dotnetIndex = script.IndexOf("exec dotnet run", StringComparison.Ordinal);

        Assert.DoesNotContain("export PATH=", script, StringComparison.Ordinal);
        Assert.True(dirnameIndex >= 0, "worktree adapter must resolve its repository root");
        Assert.True(dotnetIndex > dirnameIndex, "repository root resolution must precede the CLI invocation");
        Assert.DoesNotContain("BRANCH=", script, StringComparison.Ordinal);
        Assert.Contains("--kind \"$KIND\"", script, StringComparison.Ordinal);
        Assert.Contains("--name \"$NAME\"", script, StringComparison.Ordinal);
        Assert.DoesNotContain("case \"$KIND\" in", script, StringComparison.Ordinal);
        Assert.DoesNotContain("NAME must be", script, StringComparison.Ordinal);
        Assert.DoesNotContain("harness/$NAME", script, StringComparison.Ordinal);
    }
}
