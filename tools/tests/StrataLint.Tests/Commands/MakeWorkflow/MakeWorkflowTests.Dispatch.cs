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
        // check 在干净树须锚定 merge-base(候选不能自我保护)且容忍 rc=3 预期路径。
        Assert.Contains(" check \"${CHECK_BASE_ARGS[@]}\" --candidate-lean-report ", mathGate, StringComparison.Ordinal);
        Assert.Contains("--protected-base \"$base_sha\"", mathGate, StringComparison.Ordinal);
        Assert.Contains("[ \"$check_rc\" -ne 0 ] && [ \"$check_rc\" -ne 3 ]", mathGate, StringComparison.Ordinal);
        Assert.Contains(ScribeContentChecksScriptPath, mathGate, StringComparison.Ordinal);
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
        Assert.Equal(
            $"\t@BASE=\"$(BASE)\" /bin/bash {PreflightScriptPath}",
            Recipe(makefile, "preflight"));
        var worktreeRecipe = Recipe(makefile, "worktree");
        Assert.Contains(WorktreeInitScriptPath, worktreeRecipe, StringComparison.Ordinal);
        Assert.Contains("\"$(WORKTREE_DEST)\"", worktreeRecipe, StringComparison.Ordinal);
        Assert.Contains("WORKTREE_DEST = $(if $(DEST)", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("$(origin PATH)", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("$(PATH)", makefile, StringComparison.Ordinal);
        Assert.Contains("[DEST=DIR]", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("[PATH=DIR]", makefile, StringComparison.Ordinal);
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
        Assert.Contains("dotnet test $(HERE)/StrataLint.sln", testRecipe, StringComparison.Ordinal);
        Assert.DoesNotContain("--filter", testRecipe, StringComparison.Ordinal);
        Assert.Contains("$(HERE)/scripts/stratalint-selftest.sh", Recipe(makefile, "selftest"), StringComparison.Ordinal);
        Assert.Contains("$(HERE)/scripts/perf-report.sh", Recipe(makefile, "perf-report"), StringComparison.Ordinal);
        Assert.Contains("$(HERE)/../Golden/perf-budgets.toml", Recipe(makefile, "perf-report"), StringComparison.Ordinal);
        Assert.Contains("$(HERE)/scripts/clean-lanes.sh", Recipe(makefile, "clean-lanes"), StringComparison.Ordinal);
        Assert.DoesNotContain("refactor-p0-0-gate-authority", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("--old-build", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("OUT ?=", makefile, StringComparison.Ordinal);
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
    public void PreflightCoversRecognizedCiGateCommandsAndRejectsUnrecognizedOnes()
    {
        var root = TestRepositoryLayout.FindRoot();
        var workflow = File.ReadAllText(Path.Combine(root, AdmissionWorkflowPath));
        var preflight = File.ReadAllText(Path.Combine(root, PreflightScriptPath));
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        var jobs = Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
        var localEvidence = GateCommandSignatures(preflight).ToHashSet(StringComparer.Ordinal);
        var recognizedCiScripts = new List<string>();
        if (InvokesScript(preflight, ScribeContentChecksScriptPath))
        {
            localEvidence.UnionWith(GateCommandSignatures(
                File.ReadAllText(Path.Combine(root, ScribeContentChecksScriptPath))));
        }
        if (Regex.IsMatch(
            preflight,
            @"(?m)^[ \t]*make[ \t]+gate(?:[ \t]|$)",
            RegexOptions.CultureInvariant | RegexOptions.NonBacktracking))
        {
            localEvidence.UnionWith(GateCommandSignatures(
                File.ReadAllText(Path.Combine(root, LocalHarnessGateScriptPath))));
        }

        Assert.NotEmpty(jobs.Children);
        foreach (var (jobNode, definitionNode) in jobs.Children)
        {
            var job = Assert.IsType<YamlScalarNode>(jobNode).Value ?? string.Empty;
            var definition = Assert.IsType<YamlMappingNode>(definitionNode);
            Assert.True(
                definition.Children.TryGetValue(new YamlScalarNode("steps"), out var stepsNode)
                    && stepsNode is YamlSequenceNode,
                $"CI job '{job}' must define a 'steps' sequence so gate-command parity can inspect its run blocks; job-level 'uses' declarations are not inspectable here.");
            var steps = (YamlSequenceNode)stepsNode!;
            var ciCommands = new List<string>();
            foreach (var step in steps.Children.OfType<YamlMappingNode>())
            {
                if (!step.Children.TryGetValue(new YamlScalarNode("run"), out var runNode)) continue;
                var run = Assert.IsType<YamlScalarNode>(runNode).Value ?? string.Empty;
                var stepName = step.Children.TryGetValue(new YamlScalarNode("name"), out var nameNode)
                    && nameNode is YamlScalarNode name
                    ? name.Value ?? "<unnamed>"
                    : "<unnamed>";
                AssertNoUnrecognizedGateCommands(run, $"CI job '{job}' step '{stepName}'");
                ciCommands.AddRange(GateCommandSignatures(run));
                foreach (var scriptPath in CandidateWorkflowScriptPaths(run))
                {
                    recognizedCiScripts.Add(scriptPath);
                    var script = File.ReadAllText(Path.Combine(root, scriptPath));
                    AssertNoUnrecognizedGateCommands(script, $"CI script '{scriptPath}'");
                    ciCommands.AddRange(GateCommandSignatures(script));
                }
            }

            var distinctCiCommands = ciCommands
                .Distinct(StringComparer.Ordinal)
                .ToArray();

            Assert.All(
                distinctCiCommands,
                command => Assert.True(
                    localEvidence.Contains(command),
                    $"preflight does not execute CI job '{job}' command '{command}'."));
        }

        Assert.Equal(2, recognizedCiScripts.Count(path => path == InstallLeanToolchainScriptPath));
    }

    private static void AssertNoUnrecognizedGateCommands(string shell, string source)
    {
        foreach (var rawLine in shell.Split('\n'))
        {
            var line = rawLine.TrimEnd('\r');
            if (!Regex.IsMatch(
                    line,
                    """(?:dotnet[ \t]+"\$scribe"|run_scribe)[ \t]+\S+|make[ \t]+-C[ \t]+\S*tools[ \t]+\S+""",
                    RegexOptions.CultureInvariant | RegexOptions.NonBacktracking))
            {
                continue;
            }

            Assert.True(
                GateCommandSignatures(line).Any(),
                $"{source} contains an unrecognized gate command: '{line.Trim()}'.");
        }
    }

    private static bool InvokesScript(string shell, string repositoryPath) => Regex.IsMatch(
        shell,
        "(?m)^[ \\t]*/bin/bash[ \\t]+(?:\"\\$ROOT/|\"?)"
            + Regex.Escape(repositoryPath)
            + "\"?(?:[ \\t]+\\\\)?[ \\t]*$",
        RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);

    private static IEnumerable<string> CandidateWorkflowScriptPaths(string shell)
    {
        foreach (Match match in Regex.Matches(
            shell,
            """(?m)^[ \t]*"\$GITHUB_WORKSPACE/candidate/(?<path>tools/scripts/workflow/[A-Za-z0-9_.-]+\.sh)"[^\\\r\n]*$""",
            RegexOptions.CultureInvariant | RegexOptions.NonBacktracking))
        {
            yield return match.Groups["path"].Value;
        }
    }

    private static IEnumerable<string> GateCommandSignatures(string shell)
    {
        foreach (Match match in Regex.Matches(
            shell,
            @"(?m)^[ \t]*(?:CI=true[ \t]+)?(?:STRATALINT_REQUIRE_LIVE_REPORT=1[ \t]+)?make[ \t]+-C[ \t]+(?:candidate/)?tools[ \t]+(?<target>dotnet|test|selftest)[ \t]*$",
            RegexOptions.CultureInvariant | RegexOptions.NonBacktracking))
        {
            yield return $"make -C tools {match.Groups["target"].Value}";
        }

        foreach (Match match in Regex.Matches(
            shell,
            """(?m)^[ \t]*(?:(?:STRATALINT_LEAN_REPORT="\$report"[ \t]+)?dotnet[ \t]+"\$scribe"|run_scribe)[ \t]+(?<arguments>(?:projections|emit|emit-values|describe-report)[^\r\n]*)$""",
            RegexOptions.CultureInvariant | RegexOptions.NonBacktracking))
        {
            yield return Regex.Replace(
                match.Groups["arguments"].Value.Trim(),
                @"\$(?:report|REPORT|EFFECTIVE_REPORT)",
                "$REPORT",
                RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);
        }

        var assignments = Regex.Matches(
                shell,
                """(?m)^[ \t]*(?<variable>[A-Za-z_][A-Za-z0-9_]*)="(?<path>[^"\r\n]*\.github/scripts/harness-gate\.sh)"[ \t]*$""",
                RegexOptions.CultureInvariant | RegexOptions.NonBacktracking)
            .ToDictionary(
                static match => match.Groups["variable"].Value,
                static match => match.Groups["path"].Value,
                StringComparer.Ordinal);
        foreach (var (variable, path) in assignments)
        {
            if (Regex.IsMatch(
                shell,
                "(?m)^[ \\t]*(?:[A-Za-z_][A-Za-z0-9_]*=\"[^\"\\r\\n]*\"[ \\t]+)*\"\\$"
                    + Regex.Escape(variable)
                    + "\"(?:[ \\t]+\\\\)?[ \\t]*$",
                RegexOptions.CultureInvariant | RegexOptions.NonBacktracking))
            {
                yield return $"script:{path[(path.IndexOf(".github/", StringComparison.Ordinal))..]}";
            }
        }
    }

    [Fact]
    public void ScribeContentChecksHaveOneCanonicalCommandList()
    {
        var root = TestRepositoryLayout.FindRoot();
        var canonicalPath = Path.Combine(root, ScribeContentChecksScriptPath);
        Assert.True(File.Exists(canonicalPath), $"canonical Scribe content check script is missing: {ScribeContentChecksScriptPath}");

        var canonical = File.ReadAllText(canonicalPath);
        var mathGate = File.ReadAllText(Path.Combine(root, "tools", "scripts", "workflow", "math-gate.sh"));
        var preflight = File.ReadAllText(Path.Combine(root, PreflightScriptPath));
        var workflow = File.ReadAllText(Path.Combine(root, AdmissionWorkflowPath));
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        var jobs = Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
        var leanInspect = Assert.IsType<YamlMappingNode>(jobs.Children[new YamlScalarNode("lean-inspect")]);
        var steps = Assert.IsType<YamlSequenceNode>(leanInspect.Children[new YamlScalarNode("steps")]);
        var contentStep = Assert.Single(
            steps.Children.OfType<YamlMappingNode>(),
            step => step.Children.TryGetValue(new YamlScalarNode("name"), out var name)
                && name is YamlScalarNode { Value: "Run complete mathematical content checks" });
        var ciRun = Assert.IsType<YamlScalarNode>(contentStep.Children[new YamlScalarNode("run")]).Value!;

        AssertNoUnrecognizedGateCommands(canonical, $"canonical script '{ScribeContentChecksScriptPath}'");
        AssertNoUnrecognizedGateCommands(ciRun, "CI step 'Run complete mathematical content checks'");
        var canonicalCommands = GateCommandSignatures(canonical).ToArray();
        var ciCommands = GateCommandSignatures(ciRun).ToArray();
        Assert.Equal(
            [
                "projections --check --report \"$REPORT\"",
                "emit --check \"${DELTA_ARGS[@]}\"",
                "emit-values --check \"${DELTA_ARGS[@]}\"",
                "describe-report --check",
            ],
            canonicalCommands);
        Assert.Equal(canonicalCommands, ciCommands);
        Assert.Contains(ScribeContentChecksScriptPath, mathGate, StringComparison.Ordinal);
        Assert.Contains(
            "'exec /bin/bash \"$1\" \"${STRATALINT_LEAN_REPORT:?}\"'",
            mathGate,
            StringComparison.Ordinal);
        Assert.Contains(
            "export STRATALINT_SCRIBE_BASE=\"$base_sha\"",
            mathGate,
            StringComparison.Ordinal);
        Assert.Contains(ScribeContentChecksScriptPath, preflight, StringComparison.Ordinal);
        Assert.Contains(
            "STRATALINT_SCRIBE_BASE=\"$BASE_SHA\"",
            preflight,
            StringComparison.Ordinal);
        Assert.DoesNotContain(ScribeContentChecksScriptPath, ciRun, StringComparison.Ordinal);
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
        var directToolsResult = BoundedProcessRunner.Run(
            "make",
            ["-f", "tools/Makefile", "help"],
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
        Assert.Equal(0, directToolsResult.ExitCode);
        var directToolsOutput = System.Text.Encoding.UTF8.GetString(directToolsResult.StandardOutput);
        Assert.All(
            ToolsTargets,
            target => Assert.Contains($"make -C tools {target}", directToolsOutput, StringComparison.Ordinal));
    }
}
