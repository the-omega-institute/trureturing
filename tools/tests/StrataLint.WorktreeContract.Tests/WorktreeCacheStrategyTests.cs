using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.WorktreeContract.Tests;

[Collection("Lean cache environment")]
public sealed class WorktreeCacheStrategyTests
{
    [Fact]
    public void WorktreeToolingKeepsItsPathContractAndNeverWalksTheCacheTreePerFile()
    {
        var root = TestRepositoryLayout.FindRoot();
        var makefile = File.ReadAllText(Path.Combine(root, "Makefile"));
        var init = File.ReadAllText(Path.Combine(root, "tools", "scripts", "worktree-init.sh"));
        var clean = File.ReadAllText(Path.Combine(root, "tools", "scripts", "clean-lanes.sh"));

        Assert.Contains("WORKTREE_DEST = $(if $(DEST)", makefile, StringComparison.Ordinal);
        Assert.Contains("[DEST=DIR]", makefile, StringComparison.Ordinal);
        Assert.Contains("\"$(KIND)\" \"$(NAME)\"", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("$(origin PATH)", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("BRANCH=", init, StringComparison.Ordinal);
        Assert.Contains("--kind \"$KIND\"", init, StringComparison.Ordinal);
        Assert.Contains("--name \"$NAME\"", init, StringComparison.Ordinal);
        Assert.Contains("exec dotnet run", init, StringComparison.Ordinal);
        Assert.DoesNotContain("case \"$KIND\" in", init, StringComparison.Ordinal);
        Assert.DoesNotContain("NAME must be", init, StringComparison.Ordinal);
        Assert.DoesNotContain("harness/$NAME", init, StringComparison.Ordinal);
        Assert.DoesNotContain("export PATH=", init, StringComparison.Ordinal);
        Assert.DoesNotContain("export PATH=", clean, StringComparison.Ordinal);

        // Guard executable tooling; prose and truth data are not copy implementations.
        // The registered inputs also select this test and bind its reusable evidence.
        using var registry = JsonDocument.Parse(File.ReadAllText(Path.Combine(root, "Meta", "engineering-projects.json")));
        var registration = registry.RootElement.GetProperty("projects").EnumerateArray().Single(project =>
            project.GetProperty("path").GetString() ==
                "tools/tests/StrataLint.WorktreeContract.Tests/StrataLint.WorktreeContract.Tests.csproj");
        var inputs = registration.GetProperty("execution_inputs").EnumerateArray()
            .Select(input => input.GetString()!).ToArray();
        Assert.NotEmpty(inputs);
        // Build rejected forms dynamically so the guard does not match itself.
        var cloneFlag = string.Concat('-', 'c');
        var recursiveFlag = string.Concat('-', 'R');
        var shellForm = $"cp {cloneFlag}";
        var argumentForm = $"\"{cloneFlag}\", \"{recursiveFlag}\"";
        var scan = TestProcessRunner.Run(
            "git",
            new[] { "grep", "-n", "-I", "-e", shellForm, "-e", argumentForm, "--" }
                .Concat(inputs.Select(input => ":(glob)" + input)).ToArray(),
            root,
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024);

        Assert.Equal(
            1,
            scan.ExitCode);
    }
}
