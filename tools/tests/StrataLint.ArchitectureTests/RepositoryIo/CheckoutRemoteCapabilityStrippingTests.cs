using YamlDotNet.RepresentationModel;

namespace StrataLint.ArchitectureTests;

public sealed class CheckoutRemoteCapabilityStrippingTests
{
    private const string StripStepName = "Strip checkout remote state";
    private static readonly string RepositoryRoot = RepositoryLayout.FindRoot();
    private static readonly IReadOnlyList<RemoteStateSource> WorkflowSources =
        GitIndexRepositoryFiles.Enumerate(RepositoryRoot)
            .Where(static file => file.RelativePath.StartsWith(".github/workflows/", StringComparison.Ordinal)
                && (file.RelativePath.EndsWith(".yml", StringComparison.Ordinal)
                    || file.RelativePath.EndsWith(".yaml", StringComparison.Ordinal)))
            .OrderBy(static file => file.RelativePath, StringComparer.Ordinal)
            .Select(static file => new RemoteStateSource(file.RelativePath, File.ReadAllText(file.FullPath)))
            .ToArray();

    [Fact]
    public void EveryActionsCheckoutIsImmediatelyFollowedByFailClosedRemoteCapabilityStripping()
    {
        var findings = WorkflowSources
            .SelectMany(static source => InspectWorkflow(source.Path, source.Content))
            .ToArray();

        Assert.Empty(findings);
    }

    [Fact]
    public void CheckoutWithCompleteRemoteCapabilityStrippingIsAccepted()
    {
        const string workflow = """
            jobs:
              test:
                steps:
                  - uses: actions/checkout@v4
                    with:
                      path: source
                  - name: Strip checkout remote state
                    shell: bash
                    env:
                      CHECKOUT_PATH: source
                    run: |
                      set -euo pipefail
                      git -C "$CHECKOUT_PATH" remote remove origin
                      git -C "$CHECKOUT_PATH" for-each-ref --format='delete %(refname)' refs/remotes/ |
                        git -C "$CHECKOUT_PATH" update-ref --stdin
                      remote_count="$(git -C "$CHECKOUT_PATH" remote | wc -l)"
                      remote_ref_count="$(git -C "$CHECKOUT_PATH" for-each-ref --format='%(refname)' refs/remotes/ | wc -l)"
                      if [[ "$remote_count" -ne 0 || "$remote_ref_count" -ne 0 ]]; then
                        exit 1
                      fi
                      head_sha="$(git -C "$CHECKOUT_PATH" rev-parse HEAD)"
                      base_sha="$(git -C "$CHECKOUT_PATH" rev-parse HEAD^1)"
                      test -n "$head_sha"
                      test -n "$base_sha"
            """;

        Assert.Empty(InspectWorkflow(".github/workflows/complete.yml", workflow));
    }

    [Fact]
    public void CheckoutWithoutImmediateRemoteCapabilityStrippingIsRejected()
    {
        const string workflow = """
            jobs:
              test:
                steps:
                  - uses: actions/checkout@v4
                    with:
                      path: source
                  - name: Run tests
                    run: make -C source test
            """;

        var finding = Assert.Single(InspectWorkflow(".github/workflows/missing.yml", workflow));

        Assert.Equal(".github/workflows/missing.yml:5", finding.Location);
        Assert.Contains("immediately followed", finding.Message, StringComparison.Ordinal);
    }

    private static IReadOnlyList<CheckoutStripFinding> InspectWorkflow(string path, string content)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(content));
        var root = Assert.IsType<YamlMappingNode>(Assert.Single(stream.Documents).RootNode);
        var jobs = Mapping(root, "jobs");
        var findings = new List<CheckoutStripFinding>();

        foreach (var job in jobs.Children.Values.OfType<YamlMappingNode>())
        {
            if (!job.Children.TryGetValue(new YamlScalarNode("steps"), out var stepsNode)
                || stepsNode is not YamlSequenceNode steps)
                continue;

            for (var index = 0; index < steps.Children.Count; index++)
            {
                if (steps.Children[index] is not YamlMappingNode checkout
                    || !Scalar(checkout, "uses").StartsWith("actions/checkout@", StringComparison.Ordinal))
                    continue;

                var checkoutLine = checked((int)checkout.Start.Line + 1);
                var checkoutPath = CheckoutPath(checkout);
                if (index + 1 >= steps.Children.Count
                    || steps.Children[index + 1] is not YamlMappingNode strip)
                {
                    findings.Add(new(path, checkoutLine,
                        "actions/checkout must be immediately followed by remote capability stripping"));
                    continue;
                }

                var missing = MissingStripContracts(strip, checkoutPath);
                if (missing.Count > 0)
                {
                    findings.Add(new(path, checkoutLine,
                        $"actions/checkout must be immediately followed by fail-closed remote capability stripping; missing: {string.Join(", ", missing)}"));
                }
            }
        }

        return findings;
    }

    private static IReadOnlyList<string> MissingStripContracts(YamlMappingNode step, string checkoutPath)
    {
        var missing = new List<string>();
        Require(Scalar(step, "name") == StripStepName, "canonical step name");
        Require(Scalar(step, "shell") == "bash", "bash shell");
        Require(step.Children.TryGetValue(new YamlScalarNode("env"), out var envNode)
            && envNode is YamlMappingNode env
            && Scalar(env, "CHECKOUT_PATH") == checkoutPath, "checkout-derived path");

        var script = Scalar(step, "run");
        Require(script.Contains("set -euo pipefail", StringComparison.Ordinal), "fail-closed shell mode");
        Require(script.Contains("git -C \"$CHECKOUT_PATH\" remote remove origin", StringComparison.Ordinal),
            "remote removal");
        Require(script.Contains("--format='delete %(refname)' refs/remotes/", StringComparison.Ordinal)
            && script.Contains("git -C \"$CHECKOUT_PATH\" update-ref --stdin", StringComparison.Ordinal),
            "remote-ref deletion");
        Require(script.Contains("remote_count=", StringComparison.Ordinal)
            && script.Contains("git -C \"$CHECKOUT_PATH\" remote | wc -l", StringComparison.Ordinal)
            && script.Contains("\"$remote_count\" -ne 0", StringComparison.Ordinal), "empty remote assertion");
        Require(script.Contains("remote_ref_count=", StringComparison.Ordinal)
            && script.Contains("--format='%(refname)' refs/remotes/ | wc -l", StringComparison.Ordinal)
            && script.Contains("\"$remote_ref_count\" -ne 0", StringComparison.Ordinal),
            "empty remote-ref assertion");
        Require(script.Contains("exit 1", StringComparison.Ordinal), "explicit failure exit");
        Require(script.Contains("head_sha=\"$(git -C \"$CHECKOUT_PATH\" rev-parse HEAD)\"", StringComparison.Ordinal)
            && script.Contains("test -n \"$head_sha\"", StringComparison.Ordinal), "HEAD smoke test");
        Require(script.Contains("base_sha=\"$(git -C \"$CHECKOUT_PATH\" rev-parse HEAD^1)\"", StringComparison.Ordinal)
            && script.Contains("test -n \"$base_sha\"", StringComparison.Ordinal), "HEAD^1 smoke test");
        return missing;

        void Require(bool condition, string contract)
        {
            if (!condition) missing.Add(contract);
        }
    }

    private static string CheckoutPath(YamlMappingNode checkout) =>
        checkout.Children.TryGetValue(new YamlScalarNode("with"), out var withNode)
        && withNode is YamlMappingNode with
        && Scalar(with, "path") is { Length: > 0 } path
            ? path
            : ".";

    private static YamlMappingNode Mapping(YamlMappingNode parent, string key) =>
        Assert.IsType<YamlMappingNode>(parent.Children[new YamlScalarNode(key)]);

    private static string Scalar(YamlMappingNode parent, string key) =>
        parent.Children.TryGetValue(new YamlScalarNode(key), out var node)
        && node is YamlScalarNode scalar
            ? scalar.Value ?? string.Empty
            : string.Empty;

    private sealed record CheckoutStripFinding(string Path, int Line, string Message)
    {
        internal string Location => $"{Path}:{Line}";
        public override string ToString() => $"{Location}: {Message}";
    }
}
