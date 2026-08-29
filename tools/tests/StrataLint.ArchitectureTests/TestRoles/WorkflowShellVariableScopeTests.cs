using System.Text.RegularExpressions;
using YamlDotNet.RepresentationModel;
using StrataLint.Engine;
using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

public sealed class WorkflowShellVariableScopeTests
{
    private static readonly Regex ShellReference = new(
        @"\$(?:\{(?<braced>[A-Za-z_][A-Za-z0-9_]*)(?:[^}\r\n]*)\}|(?<simple>[A-Za-z_][A-Za-z0-9_]*))",
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
    private static readonly Regex MapfileBinding = new(
        @"(?m)^\s*mapfile\b[^\r\n]*?\s(?<name>[A-Za-z_][A-Za-z0-9_]*)\s*(?:<|$)",
        RegexOptions.CultureInvariant);
    private static readonly Regex GithubEnvWrite = new(
        @"(?m)^\s*(?:echo|printf)\b[^\r\n]*?[""'](?<name>[A-Za-z_][A-Za-z0-9_]*)=[^\r\n]*>>\s*[""']?\$(?:GITHUB_ENV|\{GITHUB_ENV\})[""']?\s*$",
        RegexOptions.CultureInvariant);
    private static readonly Regex Heredoc = new(
        @"(?m)(?<!<)<<-?\s*[""']?[A-Za-z_][A-Za-z0-9_]*",
        RegexOptions.CultureInvariant);
    private static readonly Regex NestedCommandSubstitution = new(
        @"\$\([^()\r\n]*\$\(",
        RegexOptions.CultureInvariant);
    private static readonly Regex ArithmeticExpansion = new(
        @"\$\(\(",
        RegexOptions.CultureInvariant);
    private static readonly Regex ShellBracedExpansion = new(
        @"\$\{(?!\{)(?<body>[^}\r\n]*)\}",
        RegexOptions.CultureInvariant);
    private static readonly Regex SimpleBracedVariable = new(
        @"^[A-Za-z_][A-Za-z0-9_]*$",
        RegexOptions.CultureInvariant);
    private static readonly Regex SupportedArrayExpansion = new(
        @"^(?:#?[A-Za-z_][A-Za-z0-9_]*\[(?:@|\*)\]|[A-Za-z_][A-Za-z0-9_]*\[(?:[0-9]+|\$[A-Za-z_][A-Za-z0-9_]*)\])$",
        RegexOptions.CultureInvariant);
    private static readonly Regex ArraySubscriptReference = new(
        @"\$\{[A-Za-z_][A-Za-z0-9_]*\[\$(?<name>[A-Za-z_][A-Za-z0-9_]*)\]\}",
        RegexOptions.CultureInvariant);
    private static readonly Regex ArrayLengthReference = new(
        @"\$\{#(?<name>[A-Za-z_][A-Za-z0-9_]*)\[(?:@|\*)\]\}",
        RegexOptions.CultureInvariant);
    private static readonly Regex UnclosedShellBracedExpansion = new(
        @"\$\{(?!\{)[^}\r\n]*(?:\r?\n|$)",
        RegexOptions.CultureInvariant);

    // GitHub Actions default environment variables:
    // https://docs.github.com/actions/reference/workflows-and-actions/variables#default-environment-variables
    private static readonly HashSet<string> RunnerProvidedVariables = new(StringComparer.Ordinal)
    {
        "CI", "GITHUB_ACTION", "GITHUB_ACTION_PATH", "GITHUB_ACTION_REPOSITORY", "GITHUB_ACTIONS",
        "GITHUB_ACTOR", "GITHUB_ACTOR_ID", "GITHUB_API_URL", "GITHUB_BASE_REF", "GITHUB_ENV",
        "GITHUB_EVENT_NAME", "GITHUB_EVENT_PATH", "GITHUB_GRAPHQL_URL", "GITHUB_HEAD_REF", "GITHUB_JOB",
        "GITHUB_OUTPUT", "GITHUB_PATH", "GITHUB_REF", "GITHUB_REF_NAME", "GITHUB_REF_PROTECTED",
        "GITHUB_REF_TYPE", "GITHUB_REPOSITORY", "GITHUB_REPOSITORY_ID", "GITHUB_REPOSITORY_OWNER",
        "GITHUB_REPOSITORY_OWNER_ID", "GITHUB_RETENTION_DAYS", "GITHUB_RUN_ATTEMPT", "GITHUB_RUN_ID",
        "GITHUB_RUN_NUMBER", "GITHUB_SERVER_URL", "GITHUB_SHA", "GITHUB_STEP_SUMMARY",
        "GITHUB_TRIGGERING_ACTOR", "GITHUB_WORKFLOW", "GITHUB_WORKFLOW_REF", "GITHUB_WORKFLOW_SHA",
        "GITHUB_WORKSPACE", "RUNNER_ARCH", "RUNNER_DEBUG", "RUNNER_ENVIRONMENT", "RUNNER_NAME",
        "RUNNER_OS", "RUNNER_TEMP", "RUNNER_TOOL_CACHE",
        // HOME and PATH are process environment inputs; PIPESTATUS is a Bash-maintained special array.
        "HOME", "PATH", "PIPESTATUS",
    };
    // GitHub-hosted Ubuntu image metadata exported by actions/runner-images:
    // https://github.com/actions/runner-images/blob/main/images/ubuntu/scripts/build/configure-environment.sh
    private static readonly HashSet<string> HostedRunnerImageVariables = new(StringComparer.Ordinal)
    {
        "ImageOS", "ImageVersion",
    };

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

    [Fact]
    public void UnquotedCrossStepReferenceIsRejected()
    {
        const string workflow = "jobs:\n  check:\n    steps:\n      - run: value=one\n      - name: Unquoted\n        run: echo $value\n";

        var violation = Assert.Single(FindViolations(workflow));
        Assert.Contains("value", violation, StringComparison.Ordinal);
    }

    [Fact]
    public void BracedCrossStepReferenceIsRejected()
    {
        const string workflow = "jobs:\n  check:\n    steps:\n      - run: value=one\n      - name: Braced\n        run: echo ${value}\n";

        var violation = Assert.Single(FindViolations(workflow));
        Assert.Contains("value", violation, StringComparison.Ordinal);
    }

    [Fact]
    public void HeredocIsReportedAsAnUnrecognizedConstruct()
    {
        const string workflow = "jobs:\n  check:\n    steps:\n      - name: Heredoc\n        run: |\n          cat <<EOF\n          $value\n          EOF\n";

        var violation = Assert.Single(FindViolations(workflow));
        Assert.Contains("unrecognized construct", violation, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("heredoc", violation, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void NestedCommandSubstitutionIsReportedAsAnUnrecognizedConstruct()
    {
        const string workflow = "jobs:\n  check:\n    steps:\n      - name: Nested substitution\n        run: echo \"$(outer $(inner))\"\n";

        var violation = Assert.Single(FindViolations(workflow));
        Assert.Contains("unrecognized construct", violation, StringComparison.OrdinalIgnoreCase);
        Assert.Contains("nested command substitution", violation, StringComparison.OrdinalIgnoreCase);
    }

    [Theory]
    [InlineData("echo ${value:-fallback}", "parameter expansion")]
    [InlineData("echo $((1 + 2))", "arithmetic expansion")]
    [InlineData("echo ${!name}", "indirect expansion")]
    public void UnsupportedDollarConstructIsReportedAsUnrecognized(string run, string construct)
    {
        var workflow = $"jobs:\n  check:\n    steps:\n      - name: Unsupported\n        run: {run}\n";

        var violation = Assert.Single(FindViolations(workflow));
        Assert.Contains("unrecognized construct", violation, StringComparison.OrdinalIgnoreCase);
        Assert.Contains(construct, violation, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void SimpleBoundReferencesRemainAccepted()
    {
        const string workflow = "jobs:\n  check:\n    steps:\n      - name: Simple\n        run: |\n          value=one\n          echo \"$value ${value}\"\n";

        Assert.Empty(FindViolations(workflow));
    }

    [Fact]
    public void UnboundReferenceInsideCommandSubstitutionIsRejected()
    {
        const string workflow = "jobs:\n  check:\n    steps:\n      - name: Substitution\n        run: echo \"$(printf %s $value)\"\n";

        var violation = Assert.Single(FindViolations(workflow));
        Assert.Contains("value", violation, StringComparison.Ordinal);
    }

    [Fact]
    public void KnownHostedRunnerImageVariableIsAccepted()
    {
        const string workflow = "jobs:\n  check:\n    steps:\n      - name: Runner image\n        run: echo \"$ImageOS $ImageVersion\"\n";

        Assert.Empty(FindViolations(workflow));
    }

    [Fact]
    public void UnknownRunnerPrefixedVariableIsRejected()
    {
        const string workflow = "jobs:\n  check:\n    steps:\n      - name: Unknown runner variable\n        run: echo \"$RUNNER_PRIVATE_VALUE\"\n";

        var violation = Assert.Single(FindViolations(workflow));
        Assert.Contains("RUNNER_PRIVATE_VALUE", violation, StringComparison.Ordinal);
    }

    [Fact]
    public void MentioningGithubEnvDoesNotCreateACrossStepBinding()
    {
        const string workflow = "jobs:\n  check:\n    steps:\n      - run: echo \"VALUE=one\" \"$GITHUB_ENV\"\n      - name: Not exported\n        run: echo \"$VALUE\"\n";

        var violation = Assert.Single(FindViolations(workflow));
        Assert.Contains("VALUE", violation, StringComparison.Ordinal);
    }

    [Fact]
    public void RepositoryWorkflowRunStepsBindEveryQuotedShellVariable()
    {
        var workflow = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create(".github/workflows/ci.yml"));
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
                available.UnionWith(MapfileBinding.Matches(run).Select(static match => match.Groups["name"].Value));
                foreach (Match match in ReadBinding.Matches(run))
                    available.UnionWith(match.Groups["names"].Value.Split(' ', StringSplitOptions.RemoveEmptyEntries));

                var name = TryScalar(stepNode, "name", out var stepName) ? stepName : "<unnamed>";
                var unrecognized = UnrecognizedConstruct(run);
                if (unrecognized is not null)
                {
                    violations.Add($"step '{name}' contains unrecognized construct: {unrecognized}");
                    continue;
                }
                var references = ShellReference.Matches(run)
                    .Select(static match => match.Groups["braced"].Success
                        ? match.Groups["braced"].Value
                        : match.Groups["simple"].Value)
                    .Concat(ArraySubscriptReference.Matches(run).Select(static match => match.Groups["name"].Value))
                    .Concat(ArrayLengthReference.Matches(run).Select(static match => match.Groups["name"].Value));
                foreach (var variable in references
                    .Distinct(StringComparer.Ordinal))
                {
                    if (available.Contains(variable) || IsRunnerProvided(variable)) continue;
                    violations.Add($"step '{name}' references ${variable} without a binding in that step");
                }

                inherited.UnionWith(GithubEnvWrite.Matches(run).Select(static match => match.Groups["name"].Value));
            }
        }
        return violations;
    }

    private static string? UnrecognizedConstruct(string run)
    {
        if (Heredoc.IsMatch(run)) return "heredoc";
        if (NestedCommandSubstitution.IsMatch(run)) return "nested command substitution";
        if (ArithmeticExpansion.IsMatch(run)) return "arithmetic expansion";
        foreach (Match match in ShellBracedExpansion.Matches(run))
        {
            var body = match.Groups["body"].Value;
            if (body.StartsWith('!')) return "indirect expansion";
            if (!SimpleBracedVariable.IsMatch(body) && !SupportedArrayExpansion.IsMatch(body))
                return "parameter expansion";
        }
        if (UnclosedShellBracedExpansion.IsMatch(run)) return "malformed parameter expansion";
        return null;
    }

    private static bool IsRunnerProvided(string name) =>
        RunnerProvidedVariables.Contains(name) || HostedRunnerImageVariables.Contains(name);

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
