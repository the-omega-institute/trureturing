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
            " c0-renew --base \"$(BASE)\"",
            Recipe(makefile, "c0-renew"),
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
        Assert.Contains("emit-check: echo-verify", makefile, StringComparison.Ordinal);
        Assert.Contains(ScribeScriptPath + " check", Recipe(makefile, "emit-check"), StringComparison.Ordinal);
        Assert.DoesNotContain("ingest: emit-check", makefile, StringComparison.Ordinal);
        Assert.Contains(IngestScriptPath, Recipe(makefile, "ingest"), StringComparison.Ordinal);
        Assert.Contains(
            EchoResidualSummaryScriptPath,
            Recipe(makefile, "echo-residual-summary"),
            StringComparison.Ordinal);
        Assert.Contains(EchoVerifyScriptPath, Recipe(makefile, "echo-verify"), StringComparison.Ordinal);
        Assert.Contains("golden-record", Recipe(makefile, "record-golden"), StringComparison.Ordinal);
        Assert.Contains(SelftestScriptPath, Recipe(makefile, "selftest"), StringComparison.Ordinal);
        Assert.Contains("stratalint-c0-renew-", Recipe(makefile, "scratch-sweep"), StringComparison.Ordinal);
        Assert.Contains(LocalHarnessGateScriptPath, Recipe(makefile, "gate"), StringComparison.Ordinal);
        Assert.Contains(PerfReportScriptPath, Recipe(makefile, "perf-report"), StringComparison.Ordinal);
        Assert.Contains("Golden/perf-budgets.toml", Recipe(makefile, "perf-report"), StringComparison.Ordinal);
        Assert.Contains(WorktreeInitScriptPath, Recipe(makefile, "worktree"), StringComparison.Ordinal);
        Assert.Equal(
            $"\t@/bin/bash {PrShepherdScriptPath} watch $(INTERVAL) $(CYCLES)",
            Recipe(makefile, "pr-watch"));
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
        var prWatchHelp = Assert.Single(
            output.Split('\n'),
            static line => line.StartsWith("make pr-watch ", StringComparison.Ordinal));
        var policyClauses = prWatchHelp.Split(
            ';',
            StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries);
        var stalePolicyClause = Assert.Single(
            policyClauses,
            static clause => Regex.IsMatch(
                clause,
                @"\bstale\b",
                RegexOptions.CultureInvariant));
        Assert.All(
            new[]
            {
                @"\bstale\b",
                @"\bBEHIND\b",
                @"\bCONFLICTING\b",
                @"\bpersistent-worktree\b",
                @"\bpath classification\b",
                @"\b(?:regen|recompute)\b",
                @"\b(?:alert|warn)\b",
            },
            pattern => Assert.Matches(
                new Regex(pattern, RegexOptions.CultureInvariant),
                stalePolicyClause));
        var updateBranchClause = Assert.Single(
            policyClauses,
            static clause => Regex.IsMatch(
                clause,
                @"\bother\s+BEHIND\b",
                RegexOptions.CultureInvariant));
        Assert.All(
            new[] { @"\bother\s+BEHIND\b", @"\bupdate-branch\b" },
            pattern => Assert.Matches(
                new Regex(pattern, RegexOptions.CultureInvariant),
                updateBranchClause));
        Assert.DoesNotMatch(
            new Regex(
                @"\b(?:do\s+not|never|excludes|disables|prevents)\b",
                RegexOptions.CultureInvariant | RegexOptions.IgnoreCase),
            prWatchHelp);
    }
}
