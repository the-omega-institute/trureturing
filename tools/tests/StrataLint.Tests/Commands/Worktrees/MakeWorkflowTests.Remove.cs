using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    [Fact]
    public void WorktreeRemoveUsesOneRecipeAndPassesNamesAsLiteralBytes()
    {
        var makefile = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "Makefile"));
        Assert.Equal(1, RecipeCount(makefile, "worktree-remove"));
        using var fixture = new TemporaryDirectory();
        var names = "trureturing-one\tcustom-two $(shell touch make-expanded) `touch shell-expanded` $(touch shell-substitution) \"quoted\" 'literal';\nlast";
        var result = RunRemoveMake(fixture.Path, makefile, names, 0);
        Assert.Equal(0, result.ExitCode);
        Assert.Equal(new[] { "run", "--project", "tools/StrataLint.Cli/StrataLint.Cli.csproj", "--configuration", "Release", "--",
            "worktree", "remove", "--names", names, "" }, Encoding.UTF8.GetString(result.StandardOutput).Split('\0'));
        Assert.False(RemoveMakeMarkerExists(fixture.Path));
    }

    [Fact]
    public void WorktreeRemoveIgnoresCommandLineOverrideOfInternalNames()
    {
        var makefile = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "Makefile"));
        using var fixture = new TemporaryDirectory();
        var result = RunRemoveMake(fixture.Path, makefile, "wanted", 0, "WORKTREE_REMOVE_NAMES=other");
        Assert.Equal(0, result.ExitCode);
        Assert.Equal(new[] { "run", "--project", "tools/StrataLint.Cli/StrataLint.Cli.csproj", "--configuration", "Release", "--",
            "worktree", "remove", "--names", "wanted", "" }, Encoding.UTF8.GetString(result.StandardOutput).Split('\0'));
    }

    [Theory]
    [InlineData(64)]
    [InlineData(65)]
    [InlineData(66)]
    [InlineData(67)]
    [InlineData(68)]
    [InlineData(69)]
    [InlineData(74)]
    public void WorktreeRemoveMakeReturnsItsOwn2ForClassifiedCliFailures(int cliExit)
    {
        var makefile = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "Makefile"));
        using var fixture = new TemporaryDirectory();
        var result = RunRemoveMake(fixture.Path, makefile, "", cliExit);
        Assert.Equal(2, result.ExitCode);
        Assert.EndsWith($"WORKTREE_REMOVE_RESULT exit={cliExit} removed=0 failed=0 refused=0\n",
            Encoding.UTF8.GetString(result.StandardOutput), StringComparison.Ordinal);
    }

    // Temporary fixture reads stay in helpers, outside the repository test-map selector.
    private static bool RemoveMakeMarkerExists(string path) =>
        File.Exists(Path.Combine(path, "make-expanded"))
        || File.Exists(Path.Combine(path, "shell-expanded"))
        || File.Exists(Path.Combine(path, "shell-substitution"));

    private static ProcessOutput RunRemoveMake(string path, string makefile, string names, int cliExit, params string[] makeArguments)
    {
        File.WriteAllText(Path.Combine(path, "Makefile"), makefile);
        var dotnet = Path.Combine(path, "dotnet");
        File.WriteAllText(dotnet, "#!/bin/bash\n"
            + (cliExit == 0 ? "printf '%s\\0' \"$@\"\n"
                : $"printf '%s\\n' 'WORKTREE_REMOVE_RESULT exit={cliExit} removed=0 failed=0 refused=0'\n")
            + $"exit {cliExit}\n");
        if (!OperatingSystem.IsWindows())
            File.SetUnixFileMode(dotnet, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        return TestProcessRunner.Run("/usr/bin/env", [$"PATH={path}:/usr/bin:/bin", "make", "--no-print-directory", "worktree-remove", $"NAMES={names}", .. makeArguments],
            path, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
    }
}
