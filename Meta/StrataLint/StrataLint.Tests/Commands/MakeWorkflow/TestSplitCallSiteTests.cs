using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TestSplitCallSiteTests
{
    [Fact]
    public void EveryEngineeringTestCallSiteUsesTheUnfilteredAllTarget()
    {
        var root = FindRepositoryRoot();
        var workflow = File.ReadAllText(Path.Combine(root, ".github", "workflows", "ci.yml"));
        var preflight = File.ReadAllText(Path.Combine(root, "Meta/StrataLint/scripts/preflight.sh"));
        var localGate = File.ReadAllText(Path.Combine(root, "Meta/StrataLint/scripts/local-harness-gate.sh"));

        Assert.Contains("make -C candidate test-harness", workflow, StringComparison.Ordinal);
        Assert.Contains("make -C candidate test\n", workflow, StringComparison.Ordinal);
        Assert.Contains("CI=true STRATALINT_REQUIRE_LIVE_REPORT=1 make test-all", preflight, StringComparison.Ordinal);
        Assert.DoesNotContain("STRATALINT_REQUIRE_LIVE_REPORT=1 make test\n", preflight, StringComparison.Ordinal);
        Assert.Contains("124|129|130|143", preflight, StringComparison.Ordinal);
        Assert.DoesNotContain("for suffix in '' .sha256 .input.attestation .provenance.json", workflow, StringComparison.Ordinal);
        foreach (var stepName in new[]
        {
            "Serve both canonical Lean reports from the cached address",
            "Install canonical Lean report and run projection checks",
            "Stage candidate canonical Lean report cache",
        })
        {
            var step = WorkflowStep(workflow, stepName);
            Assert.Contains("report-consumer.sh", step, StringComparison.Ordinal);
            Assert.Contains("--bundle-suffixes", step, StringComparison.Ordinal);
        }
        var ingest = File.ReadAllText(Path.Combine(root, ".github", "workflows", "theory-ingest.yml"));
        var install = WorkflowStep(ingest, "Install and verify base canonical Lean report");
        Assert.Contains("report-consumer.sh", install, StringComparison.Ordinal);
        Assert.Contains("--bundle-suffixes", install, StringComparison.Ordinal);

        var policy = LocalGatePolicy.Parse(localGate);
        Assert.Null(policy.Validate());
        Assert.Equal(["make", "-C", "$CANDIDATE_ROOT", "test-harness"], policy.Stage("engineering-test").Argv);
        Assert.Equal(["make", "-C", "$CANDIDATE_ROOT", "test"], policy.Stage("projection-check").Argv);

        var swapped = localGate.Replace(
            "run_stage lean-reports \\\n  \"$PAIR_PRODUCER\"",
            "run_stage projection-check make -C \"$CANDIDATE_ROOT\" test\nrun_stage lean-reports \\\n  \"$PAIR_PRODUCER\"",
            StringComparison.Ordinal).Replace(
            "run_stage projection-check make -C \"$CANDIDATE_ROOT\" test\nGATE=",
            "GATE=",
            StringComparison.Ordinal);
        Assert.Equal(
            "顺序违规: engineering-test < lean-reports < projection-check < admission",
            LocalGatePolicy.Parse(swapped).Validate());
    }

    [Fact]
    public void TestAllUsesExplicitInfrastructureExitPrecedenceAndSummary()
    {
        var recipe = File.ReadAllText(Path.Combine(FindRepositoryRoot(), "Makefile"));
        var testAll = recipe[(recipe.IndexOf("test-all:", StringComparison.Ordinal))..]
            .Split("\n\n", StringSplitOptions.None)[0];
        Assert.Contains("test-all: test-harness=$$rc1 test=$$rc2", testAll, StringComparison.Ordinal);
        Assert.Contains("for code in 124 126 127 129 130 143", testAll, StringComparison.Ordinal);
        Assert.Contains("exit \"$$infra\"", testAll, StringComparison.Ordinal);
        Assert.Contains("if [ \"$$rc1\" -ne 0 ] || [ \"$$rc2\" -ne 0 ]; then exit 1", testAll, StringComparison.Ordinal);
        Assert.DoesNotContain("exit $$((rc1 | rc2))", testAll, StringComparison.Ordinal);
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }

    private static string WorkflowStep(string workflow, string name) =>
        workflow.Split($"      - name: {name}\n", StringSplitOptions.None)[1]
            .Split("      - name: ", StringSplitOptions.None)[0];

}

internal sealed record LocalGateStage(string Name, IReadOnlyList<string> Argv);

internal sealed class LocalGatePolicy(IReadOnlyList<LocalGateStage> stages, int admissionIndex)
{
    internal LocalGateStage Stage(string name) => stages.Single(stage => stage.Name == name);

    internal string? Validate()
    {
        var engineering = stages.ToList().FindIndex(stage => stage.Name == "engineering-test");
        var reports = stages.ToList().FindIndex(stage => stage.Name == "lean-reports");
        var projection = stages.ToList().FindIndex(stage => stage.Name == "projection-check");
        if (engineering < 0 || reports < 0 || projection < 0 || admissionIndex < 0
            || engineering >= reports || reports >= projection || projection >= admissionIndex)
            return "顺序违规: engineering-test < lean-reports < projection-check < admission";
        if (!Stage("engineering-test").Argv.SequenceEqual(["make", "-C", "$CANDIDATE_ROOT", "test-harness"])
            || !Stage("projection-check").Argv.SequenceEqual(["make", "-C", "$CANDIDATE_ROOT", "test"]))
            return "argv 违规: local gate stage command is not the canonical target";
        return null;
    }

    internal static LocalGatePolicy Parse(string script)
    {
        var stages = new List<LocalGateStage>();
        var lines = script.Replace("\r\n", "\n", StringComparison.Ordinal).Split('\n');
        var functionDepth = 0;
        var admissionIndex = -1;
        for (var i = 0; i < lines.Length; i++)
        {
            var line = lines[i];
            if (functionDepth == 0 && line.Contains("GATE=\"$JUDGE_ROOT/.github/scripts/harness-gate.sh\"", StringComparison.Ordinal))
                admissionIndex = stages.Count;
            if (functionDepth == 0)
            {
                var match = System.Text.RegularExpressions.Regex.Match(
                    line, @"^\s*run_stage\s+(?<name>[A-Za-z0-9_-]+)(?:\s+(?<args>.*))?$",
                    System.Text.RegularExpressions.RegexOptions.CultureInvariant);
                if (match.Success)
                {
                    var command = match.Groups["args"].Value.TrimEnd();
                    while (command.EndsWith('\\') && i + 1 < lines.Length)
                        command = command[..^1].TrimEnd() + " " + lines[++i].Trim();
                    stages.Add(new LocalGateStage(match.Groups["name"].Value, ShellTokens(command)));
                }
            }
            if (line.Contains("() {", StringComparison.Ordinal)) functionDepth++;
            if (functionDepth > 0 && line.Trim() == "}") functionDepth--;
        }
        return new LocalGatePolicy(stages, admissionIndex);
    }

    private static IReadOnlyList<string> ShellTokens(string command) =>
        System.Text.RegularExpressions.Regex.Matches(command,
                @"(""([^""]*)""|'([^']*)'|([^\s]+))",
                System.Text.RegularExpressions.RegexOptions.CultureInvariant)
            .Select(static match => match.Groups[2].Success
                ? match.Groups[2].Value
                : match.Groups[3].Success ? match.Groups[3].Value : match.Groups[4].Value)
            .ToArray();
}
