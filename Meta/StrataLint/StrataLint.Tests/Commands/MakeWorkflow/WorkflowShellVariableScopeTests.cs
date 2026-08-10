using System.Text.RegularExpressions;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    private static readonly Regex QuotedReference = new(
        "\\\"\\$(?<name>[A-Za-z_][A-Za-z0-9_]*)",
        RegexOptions.CultureInvariant);
    private static readonly Regex Assignment = new(
        @"(?m)^\s*(?:(?:local|export|readonly)\s+)*(?<name>[A-Za-z_][A-Za-z0-9_]*)=",
        RegexOptions.CultureInvariant);
    private static readonly Regex ReadBinding = new(
        @"(?m)^\s*read(?:\s+-[A-Za-z]+)*(?:\s+-[a-zA-Z]\s+\S+)*\s+(?<names>[A-Za-z_][A-Za-z0-9_]*(?:\s+[A-Za-z_][A-Za-z0-9_]*)*)",
        RegexOptions.CultureInvariant);
    private static readonly Regex ForBinding = new(
        @"(?m)^\s*for\s+(?<name>[A-Za-z_][A-Za-z0-9_]*)\s+in\b",
        RegexOptions.CultureInvariant);
    private static readonly Regex GithubEnvWrite = new(
        @"(?:echo|printf)[^\n]*[""'](?<name>[A-Za-z_][A-Za-z0-9_]*)=",
        RegexOptions.CultureInvariant);

    [Fact]
    public void CrossStepShellVariableReferenceIsRejected()
    {
        const string workflow = """
            jobs:
              check:
                steps:
                  - name: Define elsewhere
                    run: |
                      value=one
                  - name: Use without binding
                    run: |
                      echo "$value"
            """;

        var violation = Assert.Single(FindViolations(workflow));
        Assert.Contains("Use without binding", violation, StringComparison.Ordinal);
        Assert.Contains("value", violation, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(AdmissionWorkflowPath)]
    [InlineData(C0CeremonyWorkflowPath)]
    [InlineData(TheoryIngestWorkflowPath)]
    public void RepositoryWorkflowRunStepsBindEveryQuotedShellVariable(string relativePath)
    {
        var workflow = File.ReadAllText(Path.Combine(FindRepositoryRoot(), relativePath));
        Assert.Empty(FindViolations(workflow));
    }

    internal static IReadOnlyList<string> FindViolations(string yaml)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(yaml));
        var root = (YamlMappingNode)stream.Documents[0].RootNode;
        var workflowEnv = EnvironmentNames(root);
        var violations = new List<string>();
        if (!TryMapping(root, "jobs", out var jobs)) return violations;

        foreach (var jobEntry in jobs.Children)
        {
            if (jobEntry.Value is not YamlMappingNode job || !TrySequence(job, "steps", out var steps)) continue;
            var inherited = new HashSet<string>(workflowEnv, StringComparer.Ordinal);
            inherited.UnionWith(EnvironmentNames(job));
            foreach (var stepNode in steps.Children.OfType<YamlMappingNode>())
            {
                if (!TryScalar(stepNode, "run", out var run)) continue;
                var available = new HashSet<string>(inherited, StringComparer.Ordinal);
                available.UnionWith(EnvironmentNames(stepNode));
                available.UnionWith(Assignment.Matches(run).Select(static match => match.Groups["name"].Value));
                available.UnionWith(ForBinding.Matches(run).Select(static match => match.Groups["name"].Value));
                foreach (Match match in ReadBinding.Matches(run))
                    available.UnionWith(match.Groups["names"].Value.Split(' ', StringSplitOptions.RemoveEmptyEntries));

                var name = TryScalar(stepNode, "name", out var stepName) ? stepName : "<unnamed>";
                foreach (var variable in QuotedReference.Matches(run)
                    .Select(static match => match.Groups["name"].Value).Distinct(StringComparer.Ordinal))
                {
                    if (available.Contains(variable) || IsRunnerProvided(variable)) continue;
                    violations.Add($"step '{name}' references \"${variable}\" without a binding in that step");
                }

                inherited.UnionWith(GithubEnvWrite.Matches(run).Select(static match => match.Groups["name"].Value));
            }
        }
        return violations;
    }

    private static bool IsRunnerProvided(string name) =>
        name is "HOME" or "PATH" or "CI" || name.StartsWith("GITHUB_", StringComparison.Ordinal)
        || name.StartsWith("RUNNER_", StringComparison.Ordinal);

    private static HashSet<string> EnvironmentNames(YamlMappingNode node)
    {
        if (!TryMapping(node, "env", out var env)) return [];
        return env.Children.Keys.OfType<YamlScalarNode>()
            .Select(static key => key.Value ?? string.Empty)
            .Where(static key => key.Length > 0)
            .ToHashSet(StringComparer.Ordinal);
    }

    private static bool TryMapping(YamlMappingNode node, string key, out YamlMappingNode value)
    {
        if (node.Children.TryGetValue(new YamlScalarNode(key), out var child) && child is YamlMappingNode mapping)
        { value = mapping; return true; }
        value = null!; return false;
    }

    private static bool TrySequence(YamlMappingNode node, string key, out YamlSequenceNode value)
    {
        if (node.Children.TryGetValue(new YamlScalarNode(key), out var child) && child is YamlSequenceNode sequence)
        { value = sequence; return true; }
        value = null!; return false;
    }

    private static bool TryScalar(YamlMappingNode node, string key, out string value)
    {
        if (node.Children.TryGetValue(new YamlScalarNode(key), out var child) && child is YamlScalarNode scalar)
        { value = scalar.Value ?? string.Empty; return true; }
        value = string.Empty; return false;
    }

}
