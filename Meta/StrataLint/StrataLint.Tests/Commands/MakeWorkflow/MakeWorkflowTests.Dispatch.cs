using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    [Fact]
    public void MakefileIsAThinCompleteDispatchTable()
    {
        var root = FindRepositoryRoot();
        var makefile = File.ReadAllText(Path.Combine(root, "Makefile"));

        Assert.Contains(".DEFAULT_GOAL := help", makefile, StringComparison.Ordinal);
        var phony = Assert.Single(
            makefile.Split('\n'),
            static line => line.StartsWith(".PHONY:", StringComparison.Ordinal));
        Assert.Equal(Targets, phony[".PHONY:".Length..].Split(' ', StringSplitOptions.RemoveEmptyEntries));
        foreach (var target in Targets)
        {
            Assert.Matches(new Regex($"(?m)^{Regex.Escape(target)}:", RegexOptions.CultureInvariant), makefile);
            Assert.InRange(RecipeCount(makefile, target), 0, 1);
        }

        Assert.Contains("build: lean-cache-ensure dotnet lean", makefile, StringComparison.Ordinal);
        Assert.Equal(0, RecipeCount(makefile, "build"));
        Assert.Contains(
            " c0-verify --base \"$(BASE)\"",
            Recipe(makefile, "c0-verify"),
            StringComparison.Ordinal);
        Assert.Contains(
            " c0-reconcile-trust-root",
            Recipe(makefile, "c0-reconcile-trust-root"),
            StringComparison.Ordinal);
        Assert.Contains(CleanLanesScriptPath, Recipe(makefile, "clean-lanes"), StringComparison.Ordinal);
        Assert.Contains(DotnetBuildScriptPath, Recipe(makefile, "dotnet"), StringComparison.Ordinal);
        Assert.Contains("dotnet test", Recipe(makefile, "test"), StringComparison.Ordinal);
        Assert.Equal(
            $"\t@/bin/bash {LeanCacheEnsureScriptPath}",
            Recipe(makefile, "lean-cache-ensure"));
        Assert.Contains("lean: lean-cache-ensure", makefile, StringComparison.Ordinal);
        Assert.Contains("lake build", Recipe(makefile, "lean"), StringComparison.Ordinal);
        Assert.Contains("lean-report: lean-cache-ensure", makefile, StringComparison.Ordinal);
        Assert.Contains(LeanReportScriptPath, Recipe(makefile, "lean-report"), StringComparison.Ordinal);
        Assert.Contains(ScribeScriptPath + " emit", Recipe(makefile, "emit"), StringComparison.Ordinal);
        Assert.Contains(IngestScriptPath, Recipe(makefile, "ingest"), StringComparison.Ordinal);
        var showAtomRecipe = Recipe(makefile, "show-atom");
        Assert.Contains("dotnet run --no-build --project", showAtomRecipe, StringComparison.Ordinal);
        Assert.Contains(" show-atom --atom-id \"$(ATOM_ID)\"", showAtomRecipe, StringComparison.Ordinal);
        Assert.Contains(
            EchoResidualSummaryScriptPath,
            Recipe(makefile, "echo-residual-summary"),
            StringComparison.Ordinal);
        Assert.Contains("golden-record", Recipe(makefile, "record-golden"), StringComparison.Ordinal);
        Assert.Contains(SelftestScriptPath, Recipe(makefile, "selftest"), StringComparison.Ordinal);
        Assert.Contains("stratalint-c0-renew-", Recipe(makefile, "scratch-sweep"), StringComparison.Ordinal);
        Assert.Contains(LocalHarnessGateScriptPath, Recipe(makefile, "gate"), StringComparison.Ordinal);
        Assert.Contains(PerfReportScriptPath, Recipe(makefile, "perf-report"), StringComparison.Ordinal);
        Assert.Contains("Golden/perf-budgets.toml", Recipe(makefile, "perf-report"), StringComparison.Ordinal);
        Assert.Contains(WorktreeInitScriptPath, Recipe(makefile, "worktree"), StringComparison.Ordinal);
        Assert.Contains(PrOpenScriptPath, Recipe(makefile, "pr-open"), StringComparison.Ordinal);
        Assert.Contains("--head \"$(HEAD)\"", Recipe(makefile, "pr-open"), StringComparison.Ordinal);
        Assert.Contains(PrUpdateScriptPath, Recipe(makefile, "pr-update"), StringComparison.Ordinal);
        Assert.Contains("--pr \"$(PR)\"", Recipe(makefile, "pr-update"), StringComparison.Ordinal);
        Assert.Contains(
            " gate-authority --old-build \"$(OLD_BUILD)\" --out \"$(OUT)\"",
            Recipe(makefile, "refactor-p0-0-gate-authority"),
            StringComparison.Ordinal);
    }

    [Fact]
    public void HelpRunsAndNamesEveryTarget()
    {
        var root = FindRepositoryRoot();
        var result = BoundedProcessRunner.Run(
            "make",
            ["help"],
            root,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        Assert.Equal(0, result.ExitCode);
        var output = System.Text.Encoding.UTF8.GetString(result.StandardOutput);
        Assert.All(Targets, target => Assert.Contains($"make {target}", output, StringComparison.Ordinal));
        Assert.Contains("dry-run", output, StringComparison.Ordinal);
        Assert.Contains("FORCE=1", output, StringComparison.Ordinal);
        Assert.Contains("values", output, StringComparison.OrdinalIgnoreCase);
        var prUpdateHelp = Assert.Single(
            output.Split('\n'),
            static line => line.StartsWith("make pr-update ", StringComparison.Ordinal));
        Assert.Contains("BEHIND", prUpdateHelp, StringComparison.Ordinal);
        Assert.Contains("auto-merge armed", prUpdateHelp, StringComparison.Ordinal);
        Assert.Contains("once", prUpdateHelp, StringComparison.Ordinal);
    }
}
