using System.Text.RegularExpressions;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    [Fact]
    public void WorktreeHoldAndReleaseReuseTheWorktreeDestinationExpression()
    {
        var root = TestRepositoryLayout.FindRoot();
        var makefile = File.ReadAllText(Path.Combine(root, "Makefile"));
        var destinationDefinitions = Regex.Matches(
            makefile,
            @"(?m)^WORKTREE_DEST\s*=",
            RegexOptions.CultureInvariant);

        Assert.Single(destinationDefinitions.Cast<Match>());
        Assert.Contains(
            "WORKTREE_DEST = $(if $(DEST),$(abspath $(DEST)),$(abspath ../trureturing-$(NAME)))",
            makefile,
            StringComparison.Ordinal);

        var createRecipe = Recipe(makefile, "worktree");
        var holdRecipe = Recipe(makefile, "worktree-hold");
        var releaseRecipe = Recipe(makefile, "worktree-release");
        Assert.All(
            new[] { createRecipe, holdRecipe, releaseRecipe },
            recipe => Assert.Contains("\"$(WORKTREE_DEST)\"", recipe, StringComparison.Ordinal));
        Assert.DoesNotContain("../trureturing-", holdRecipe, StringComparison.Ordinal);
        Assert.DoesNotContain("../trureturing-", releaseRecipe, StringComparison.Ordinal);
        Assert.Contains("-- worktree hold", holdRecipe, StringComparison.Ordinal);
        Assert.Contains("--reason \"$(REASON)\"", holdRecipe, StringComparison.Ordinal);
        Assert.Contains("-- worktree release", releaseRecipe, StringComparison.Ordinal);
        Assert.DoesNotContain("git worktree", holdRecipe + releaseRecipe, StringComparison.Ordinal);
    }
}
