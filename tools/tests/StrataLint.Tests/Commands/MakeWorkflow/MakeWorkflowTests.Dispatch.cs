using System.Text.RegularExpressions;
using StrataLint.Engine;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    [Fact]
    public void EngineeringCheckRunsTheCanonicalToolsTestTargetWithoutAFilter()
    {
        var root = TestRepositoryLayout.FindRoot();
        var makefile = File.ReadAllText(Path.Combine(root, ToolsMakefilePath));
        var workflow = File.ReadAllText(Path.Combine(root, AdmissionWorkflowPath));
        var engineeringStep = EngineeringTestStep(workflow);
        var targetMatches = Regex.Matches(
            engineeringStep,
            @"(?m)^[ \t]*make[ \t]+-C[ \t]+candidate/tools[ \t]+(?<target>[A-Za-z][A-Za-z0-9_-]*)[ \t]*$",
            RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);

        Assert.True(
            targetMatches.Count == 1,
            "The candidate-engineering test step must invoke exactly one concrete make target so CI cannot silently switch to a different test lane.");
        var targetMatch = targetMatches[0];
        Assert.True(
            !engineeringStep.Contains("--filter", StringComparison.Ordinal),
            "The candidate-engineering check must call the canonical unfiltered test target; commit 5743d114 filtered Script tests and left those tests unexecuted in CI.");

        var target = targetMatch.Groups["target"].Value;
        Assert.Equal("test", target);
        var recipe = Recipe(makefile, target);
        Assert.True(
            recipe.Contains("dotnet test", StringComparison.Ordinal),
            $"The make target '{target}' called by candidate-engineering must be the .NET test target guarded by this invariant.");
        Assert.True(
            !recipe.Contains("--filter", StringComparison.Ordinal),
            $"The canonical make target '{target}' must keep its dotnet test command unfiltered; commit 5743d114 filtered Script tests and CI then had no replacement lane.");
    }

    [Fact]
    public void MakefileIsAThinCompleteDispatchTable()
    {
        var root = TestRepositoryLayout.FindRoot();
        var makefile = File.ReadAllText(Path.Combine(root, "Makefile"));

        Assert.Contains(".DEFAULT_GOAL := help", makefile, StringComparison.Ordinal);
        var phony = Assert.Single(
            makefile.Split('\n'),
            static line => line.StartsWith(".PHONY:", StringComparison.Ordinal));
        Assert.Equal(RootTargets, phony[".PHONY:".Length..].Split(' ', StringSplitOptions.RemoveEmptyEntries));
        foreach (var target in RootTargets)
        {
            Assert.Matches(new Regex($"(?m)^{Regex.Escape(target)}:", RegexOptions.CultureInvariant), makefile);
            Assert.InRange(RecipeCount(makefile, target), 0, 1);
        }

        Assert.Contains("build: lean-cache-ensure lean", makefile, StringComparison.Ordinal);
        Assert.Equal(0, RecipeCount(makefile, "build"));
        // make test 是薄委托;数学门链条的唯一真源在 math-gate.sh 里,断言脚本本体。
        var mathematicalTestRecipe = Recipe(makefile, "test");
        Assert.DoesNotContain("dotnet test", mathematicalTestRecipe, StringComparison.Ordinal);
        Assert.Contains("tools/scripts/workflow/math-gate.sh", mathematicalTestRecipe, StringComparison.Ordinal);
        var mathGate = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "scripts", "workflow", "math-gate.sh"));
        Assert.DoesNotContain("dotnet test", mathGate, StringComparison.Ordinal);
        Assert.Contains("/../../..\" && pwd -P)", mathGate, StringComparison.Ordinal);
        Assert.Contains("lake build", mathGate, StringComparison.Ordinal);
        Assert.Contains("make lean-report", mathGate, StringComparison.Ordinal);
        Assert.Contains(" check --candidate-lean-report ", mathGate, StringComparison.Ordinal);
        Assert.Contains(" projections --check --report ", mathGate, StringComparison.Ordinal);
        Assert.Contains(" emit --check", mathGate, StringComparison.Ordinal);
        Assert.Contains(" emit-values --check", mathGate, StringComparison.Ordinal);
        Assert.Contains(" describe-report --check", mathGate, StringComparison.Ordinal);
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
        Assert.Contains(LocalHarnessGateScriptPath, Recipe(makefile, "gate"), StringComparison.Ordinal);
        Assert.Contains(PreflightScriptPath, Recipe(makefile, "preflight"), StringComparison.Ordinal);
        Assert.Contains(WorktreeInitScriptPath, Recipe(makefile, "worktree"), StringComparison.Ordinal);
        Assert.Contains(PrOpenScriptPath, Recipe(makefile, "pr-open"), StringComparison.Ordinal);
        Assert.Contains("--head \"$(HEAD)\"", Recipe(makefile, "pr-open"), StringComparison.Ordinal);
        Assert.DoesNotContain("pr-update", makefile, StringComparison.Ordinal);
        foreach (var removed in ToolsTargets.Except(["help", "test"], StringComparer.Ordinal))
        {
            Assert.DoesNotContain($"\n{removed}:", "\n" + makefile, StringComparison.Ordinal);
        }
        Assert.DoesNotContain("\ntools-test:", "\n" + makefile, StringComparison.Ordinal);
    }

    [Fact]
    public void ToolsMakefileIsAThinCompleteDispatchTable()
    {
        var root = TestRepositoryLayout.FindRoot();
        var makefile = File.ReadAllText(Path.Combine(root, ToolsMakefilePath));

        Assert.Contains(".DEFAULT_GOAL := help", makefile, StringComparison.Ordinal);
        var phony = Assert.Single(
            makefile.Split('\n'),
            static line => line.StartsWith(".PHONY:", StringComparison.Ordinal));
        Assert.Equal(ToolsTargets, phony[".PHONY:".Length..].Split(' ', StringSplitOptions.RemoveEmptyEntries));
        foreach (var target in ToolsTargets)
        {
            Assert.Matches(new Regex($"(?m)^{Regex.Escape(target)}:", RegexOptions.CultureInvariant), makefile);
            Assert.InRange(RecipeCount(makefile, target), 0, 1);
        }

        Assert.Contains("scripts/dotnet-build.sh", Recipe(makefile, "dotnet"), StringComparison.Ordinal);
        var testRecipe = Recipe(makefile, "test");
        Assert.Contains("dotnet test StrataLint.sln", testRecipe, StringComparison.Ordinal);
        Assert.DoesNotContain("--filter", testRecipe, StringComparison.Ordinal);
        Assert.Contains("scripts/stratalint-selftest.sh", Recipe(makefile, "selftest"), StringComparison.Ordinal);
        Assert.Contains("scripts/perf-report.sh", Recipe(makefile, "perf-report"), StringComparison.Ordinal);
        Assert.Contains("../Golden/perf-budgets.toml", Recipe(makefile, "perf-report"), StringComparison.Ordinal);
        Assert.Contains("scripts/clean-lanes.sh", Recipe(makefile, "clean-lanes"), StringComparison.Ordinal);
        Assert.Contains(
            " gate-authority --old-build \"$(OLD_BUILD)\" --out \"$(OUT)\"",
            Recipe(makefile, "refactor-p0-0-gate-authority"),
            StringComparison.Ordinal);
    }

    private static string EngineeringTestStep(string workflow)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        var jobs = Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
        var engineering = Assert.IsType<YamlMappingNode>(
            jobs.Children[new YamlScalarNode("candidate-engineering")]);
        var steps = Assert.IsType<YamlSequenceNode>(engineering.Children[new YamlScalarNode("steps")]);
        var step = steps.Children.OfType<YamlMappingNode>().Single(candidate =>
            candidate.Children.TryGetValue(new YamlScalarNode("name"), out var name)
            && name is YamlScalarNode scalar
            && scalar.Value == "Run candidate golden and integration tests");
        return Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("run")]).Value!;
    }

    [Fact]
    public void HelpRunsAndNamesEveryTarget()
    {
        var root = TestRepositoryLayout.FindRoot();
        var rootResult = BoundedProcessRunner.Run(
            "make",
            ["help"],
            root,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        var toolsResult = BoundedProcessRunner.Run(
            "make",
            ["-C", "tools", "help"],
            root,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        Assert.Equal(0, rootResult.ExitCode);
        var rootOutput = System.Text.Encoding.UTF8.GetString(rootResult.StandardOutput);
        Assert.All(RootTargets, target => Assert.Contains($"make {target}", rootOutput, StringComparison.Ordinal));
        Assert.Contains("values", rootOutput, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("make dotnet", rootOutput, StringComparison.Ordinal);
        Assert.DoesNotContain("make tools-test", rootOutput, StringComparison.Ordinal);
        Assert.DoesNotContain("pr-update", rootOutput, StringComparison.Ordinal);

        Assert.Equal(0, toolsResult.ExitCode);
        var toolsOutput = System.Text.Encoding.UTF8.GetString(toolsResult.StandardOutput);
        Assert.All(
            ToolsTargets,
            target => Assert.Contains($"make -C tools {target}", toolsOutput, StringComparison.Ordinal));
        Assert.Contains("dry-run", toolsOutput, StringComparison.Ordinal);
        Assert.Contains("FORCE=1", toolsOutput, StringComparison.Ordinal);
        Assert.DoesNotContain("make -C tools lean", toolsOutput, StringComparison.Ordinal);
    }
}
