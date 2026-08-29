using System.Text.RegularExpressions;
using StrataLint.Engine;
using YamlDotNet.RepresentationModel;

namespace StrataLint.ScriptTests;

[ScriptSubject("tools/Makefile")]
public sealed class ToolsMakefileTests
{
    private static readonly string[] ToolsTargets =
    [
        "help",
        "dotnet",
        "test",
        "engineering-tests",
        "selftest",
        "update-renderer-contract",
        "clean-lanes",
    ];

    [Fact]
    public void EngineeringCheckUsesBaseOwnedIdentityPlanWithoutProjectRepresentatives()
    {
        var makefile = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/Makefile"));
        var workflow = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create(".github/workflows/ci.yml"));
        var engineeringStep = EngineeringTestStep(workflow);
        var targetMatches = Regex.Matches(
            engineeringStep,
            "(?m)^[ \\t]*make[ \\t]+-C[ \\t]+\"\\$base_harness_root/tools\"[ \\t]+(?<target>engineering-tests)\\b[^\\r\\n]*\\bMODE=execute\\b",
            RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);

        var target = Assert.Single(targetMatches.Cast<Match>()).Groups["target"].Value;
        Assert.Equal("engineering-tests", target);
        var recipe = Recipe(makefile, target);
        Assert.Contains("StrataLint.EngineeringScope.csproj", recipe, StringComparison.Ordinal);
        Assert.Contains("--head \"$(HEAD)\" --base \"$(BASE)\"", recipe, StringComparison.Ordinal);
        Assert.Contains("REPOSITORY=\"$GITHUB_WORKSPACE/candidate\"", engineeringStep, StringComparison.Ordinal);
        Assert.Contains("MODE=execute", engineeringStep, StringComparison.Ordinal);
        Assert.DoesNotContain("required_test_projects", engineeringStep, StringComparison.Ordinal);
        Assert.DoesNotContain("--required-assembly", engineeringStep, StringComparison.Ordinal);
        Assert.DoesNotContain("--filter", engineeringStep, StringComparison.Ordinal);
        Assert.DoesNotContain("git diff", engineeringStep, StringComparison.Ordinal);
    }

    [Fact]
    public void ToolsMakefileIsAThinCompleteDispatchTable()
    {
        var root = TestRepositoryLayout.FindRoot();
        var makefile = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/Makefile"));

        Assert.Contains(".DEFAULT_GOAL := help", makefile, StringComparison.Ordinal);
        Assert.Contains(
            "HERE := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))",
            makefile,
            StringComparison.Ordinal);
        var phony = Assert.Single(
            makefile.Split('\n'),
            static line => line.StartsWith(".PHONY:", StringComparison.Ordinal));
        Assert.Equal(ToolsTargets, phony[".PHONY:".Length..].Split(' ', StringSplitOptions.RemoveEmptyEntries));
        foreach (var target in ToolsTargets)
        {
            Assert.Matches(new Regex($"(?m)^{Regex.Escape(target)}:", RegexOptions.CultureInvariant), makefile);
            Assert.InRange(RecipeCount(makefile, target), 0, 1);
        }

        Assert.Contains("$(HERE)/scripts/dotnet-build.sh", Recipe(makefile, "dotnet"), StringComparison.Ordinal);
        var testRecipe = Recipe(makefile, "test");
        Assert.Contains("scripts/dotnet-test.sh $(HERE)/StrataLint.sln", testRecipe, StringComparison.Ordinal);
        Assert.DoesNotContain("--filter", testRecipe, StringComparison.Ordinal);
        var dotnetTest = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(), "tools/scripts/dotnet-test.sh"));
        Assert.Contains("dotnet test \"$@\"", dotnetTest, StringComparison.Ordinal);
        Assert.Contains("verify-trx --results-directory \"$RESULTS_DIRECTORY\"", dotnetTest, StringComparison.Ordinal);
        var engineeringTestsRecipe = Recipe(makefile, "engineering-tests");
        Assert.Contains("StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj", engineeringTestsRecipe, StringComparison.Ordinal);
        Assert.Contains("REPOSITORY ?= $(HERE)/..", makefile, StringComparison.Ordinal);
        Assert.Contains("--repository \"$(REPOSITORY)\"", engineeringTestsRecipe, StringComparison.Ordinal);
        Assert.Contains("$(HERE)/scripts/stratalint-selftest.sh", Recipe(makefile, "selftest"), StringComparison.Ordinal);
        Assert.Contains("$(HERE)/scripts/update-renderer-contract.sh", Recipe(makefile, "update-renderer-contract"), StringComparison.Ordinal);
        Assert.True(
            File.Exists(Path.Combine(root, "tools/scripts/update-renderer-contract.sh")),
            "tools/scripts/update-renderer-contract.sh is named by the update-renderer-contract recipe but is absent");
        Assert.Contains("$(HERE)/scripts/clean-lanes.sh", Recipe(makefile, "clean-lanes"), StringComparison.Ordinal);
        Assert.DoesNotContain("refactor-p0-0-gate-authority", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("--old-build", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("OUT ?=", makefile, StringComparison.Ordinal);
    }

    [Fact]
    public void HelpRunsAndNamesEveryToolsTarget()
    {
        var root = TestRepositoryLayout.FindRoot();
        var toolsResult = TestProcessRunner.Run(
            "make",
            ["-C", "tools", "help"],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);
        var directToolsResult = TestProcessRunner.Run(
            "make",
            ["-f", "tools/Makefile", "help"],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        Assert.Equal(0, toolsResult.ExitCode);
        var toolsOutput = System.Text.Encoding.UTF8.GetString(toolsResult.StandardOutput);
        Assert.All(ToolsTargets, target => Assert.Contains($"make -C tools {target}", toolsOutput, StringComparison.Ordinal));
        Assert.Contains("dry-run", toolsOutput, StringComparison.Ordinal);
        Assert.Contains("FORCE=1", toolsOutput, StringComparison.Ordinal);
        Assert.DoesNotContain("make -C tools lean", toolsOutput, StringComparison.Ordinal);
        Assert.Equal(0, directToolsResult.ExitCode);
        var directToolsOutput = System.Text.Encoding.UTF8.GetString(directToolsResult.StandardOutput);
        Assert.All(ToolsTargets, target => Assert.Contains($"make -C tools {target}", directToolsOutput, StringComparison.Ordinal));
    }

    private static string EngineeringTestStep(string workflow)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        var jobs = Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
        var engineering = Assert.IsType<YamlMappingNode>(jobs.Children[new YamlScalarNode("candidate-engineering")]);
        var steps = Assert.IsType<YamlSequenceNode>(engineering.Children[new YamlScalarNode("steps")]);
        var step = steps.Children.OfType<YamlMappingNode>().Single(candidate =>
            candidate.Children.TryGetValue(new YamlScalarNode("name"), out var name)
            && name is YamlScalarNode scalar
            && scalar.Value == "Replan and run engineering tests with protected-base harness");
        return Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("run")]).Value!;
    }

    private static int RecipeCount(string makefile, string target) => RecipeLines(makefile, target).Count;

    private static string Recipe(string makefile, string target) => Assert.Single(RecipeLines(makefile, target));

    private static IReadOnlyList<string> RecipeLines(string makefile, string target)
    {
        var lines = makefile.Split('\n');
        var start = Array.FindIndex(lines, line => line.StartsWith(target + ":", StringComparison.Ordinal));
        Assert.True(start >= 0, $"target is absent: {target}");
        return lines.Skip(start + 1)
            .TakeWhile(static line => line.Length == 0 || line[0] == '\t')
            .Where(static line => line.StartsWith('\t'))
            .ToArray();
    }
}
