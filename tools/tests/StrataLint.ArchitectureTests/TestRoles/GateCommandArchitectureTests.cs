using System.Text.RegularExpressions;
using StrataLint.Engine;
using YamlDotNet.RepresentationModel;

using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

public sealed class GateCommandArchitectureTests
{
    private const string ScribeContentChecksScriptPath = "tools/scripts/workflow/scribe-content-checks.sh";
    private const string InstallLeanToolchainScriptPath = "tools/scripts/workflow/install-lean-toolchain.sh";

    [Fact]
    public void PreflightCoversRecognizedCiGateCommandsAndRejectsUnrecognizedOnes()
    {
        var workflow = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            ".github/workflows/ci.yml"));
        var preflight = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools/scripts/preflight.sh"));
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        var jobs = Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
        var localEvidence = GateCommandSignatures(preflight).ToHashSet(StringComparer.Ordinal);
        var recognizedCiScripts = new List<string>();
        if (InvokesScript(preflight, ScribeContentChecksScriptPath))
        {
            localEvidence.UnionWith(GateCommandSignatures(
                File.ReadAllText(Path.Combine(
                    TestRepositoryLayout.FindRoot(),
                    "tools/scripts/workflow/scribe-content-checks.sh"))));
        }
        if (Regex.IsMatch(
            preflight,
            @"(?m)^[ \t]*make[ \t]+gate(?:[ \t]|$)",
            RegexOptions.CultureInvariant | RegexOptions.NonBacktracking))
        {
            localEvidence.UnionWith(GateCommandSignatures(
                File.ReadAllText(Path.Combine(
                    TestRepositoryLayout.FindRoot(),
                    "tools/scripts/local-harness-gate.sh"))));
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
                    Assert.Equal(InstallLeanToolchainScriptPath, scriptPath);
                    var script = File.ReadAllText(Path.Combine(
                        TestRepositoryLayout.FindRoot(),
                        "tools/scripts/workflow/install-lean-toolchain.sh"));
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
            @"(?m)^[ \t]*(?:FULL=1[ \t]+)?(?:CI=true[ \t]+)?(?:STRATALINT_REQUIRE_LIVE_REPORT=1[ \t]+)?make[ \t]+-C[ \t]+(?:candidate/)?tools[ \t]+engineering-tests[ \t]+MODE=(?<mode>plan|execute)\b[^\r\n]*$",
            RegexOptions.CultureInvariant | RegexOptions.NonBacktracking))
        {
            yield return $"make -C tools engineering-tests MODE={match.Groups["mode"].Value}";
        }

        foreach (Match match in Regex.Matches(
            shell,
            @"(?m)^[ \t]*(?:CI=true[ \t]+)?(?:STRATALINT_REQUIRE_LIVE_REPORT=1[ \t]+)?make[ \t]+-C[ \t]+(?:candidate/)?tools[ \t]+(?<target>dotnet|test|selftest)[ \t]*$",
            RegexOptions.CultureInvariant | RegexOptions.NonBacktracking))
        {
            yield return $"make -C tools {match.Groups["target"].Value}";
        }

        foreach (Match match in Regex.Matches(
            shell,
            """(?m)^[ \t]*(?:(?:STRATALINT_LEAN_REPORT="\$report"[ \t]+)?dotnet[ \t]+"\$scribe"|run_scribe)[ \t]+(?<arguments>(?:projections|emit|emit-values|describe-report|markdown-check)[^\r\n]*)$""",
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
        Assert.True(
            File.Exists(Path.Combine(
                TestRepositoryLayout.FindRoot(),
                "tools/scripts/workflow/scribe-content-checks.sh")),
            $"canonical Scribe content check script is missing: {ScribeContentChecksScriptPath}");

        var canonical = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools/scripts/workflow/scribe-content-checks.sh"));
        var mathGate = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools/scripts/workflow/math-gate.sh"));
        var preflight = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools/scripts/preflight.sh"));
        var workflow = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            ".github/workflows/ci.yml"));
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
        var canonicalCommands = GateCommandSignatures(canonical).ToArray();
        Assert.Equal(
            [
                "projections --check --report \"$REPORT\"",
                "describe-report --check",
                "markdown-check --report \"$REPORT\" --paths-from -",
            ],
            canonicalCommands);
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
        Assert.Contains(ScribeContentChecksScriptPath, ciRun, StringComparison.Ordinal);
        Assert.Contains("steps.base.outputs.sha", ciRun, StringComparison.Ordinal);
        Assert.Empty(GateCommandSignatures(ciRun));
    }

}
