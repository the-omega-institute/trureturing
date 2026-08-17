using System.Text.RegularExpressions;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Tests;

public sealed class TheoryIngestWritebackTopologyTests
{
    private const string WorkflowPath = ".github/workflows/theory-ingest.yml";

    [Fact]
    public void TheoryIngestSeparatesReadOnlyProposalFromMinimalWriteAuthorization()
    {
        var workflow = LoadWorkflow();
        var propose = Job(workflow, "propose");
        var writeback = Job(workflow, "writeback");

        Assert.Equal("Propose theory ingest closure", Scalar(propose, "name"));
        Assert.Equal("read", Scalar(Mapping(propose, "permissions"), "contents"));
        Assert.Equal("Authorize and write back theory ingest closure", Scalar(writeback, "name"));
        Assert.Equal("write", Scalar(Mapping(writeback, "permissions"), "contents"));
        Assert.Equal("propose", Scalar(writeback, "needs"));

        var proposeText = Render(propose);
        Assert.DoesNotContain("${{ secrets.", proposeText, StringComparison.Ordinal);
        Assert.DoesNotContain("${{ github.token }}", proposeText, StringComparison.Ordinal);
        Assert.Contains("make ingest BASE=${{ steps.base.outputs.sha }}", proposeText, StringComparison.Ordinal);
        Assert.Contains("actions/upload-artifact@v4", proposeText, StringComparison.Ordinal);
        Assert.Contains("theory-ingest.patch", proposeText, StringComparison.Ordinal);
    }

    [Fact]
    public void WritebackJobNeverExecutesCandidateFilesOrConsumesProposalAsCommands()
    {
        var writeback = Job(LoadWorkflow(), "writeback");
        var steps = Sequence(writeback, "steps").Children.OfType<YamlMappingNode>().ToArray();

        Assert.DoesNotContain(
            DescendantScalars(writeback),
            static value => value.Contains("needs.propose.outputs", StringComparison.Ordinal));
        Assert.DoesNotContain(
            steps,
            static step => TryScalar(step, "uses", out var uses)
                && uses.StartsWith("./", StringComparison.Ordinal));
        Assert.DoesNotContain(
            steps,
            static step => TryScalar(step, "uses", out var uses)
                && uses.StartsWith("actions/cache", StringComparison.Ordinal));
        Assert.DoesNotContain(
            steps,
            static step => TryScalar(step, "working-directory", out var directory)
                && directory.Contains("candidate", StringComparison.Ordinal));

        var scripts = steps
            .Where(static step => TryScalar(step, "run", out _))
            .Select(static step => Scalar(step, "run"))
            .ToArray();
        Assert.DoesNotContain(
            scripts,
            static script => script.Contains("candidate-data/", StringComparison.Ordinal)
                || script.Contains("cd candidate-data", StringComparison.Ordinal)
                || script.Contains("make -C candidate", StringComparison.Ordinal)
                || Regex.IsMatch(script, @"(?:bash|sh|source|exec)\s+[^\n]*candidate"));
        Assert.Contains(
            scripts,
            static script => script.Contains(
                "$GITHUB_WORKSPACE/trusted/tools/scripts/workflow/theory-ingest-closure.sh",
                StringComparison.Ordinal));

        var candidateCheckout = Assert.Single(
            steps,
            static step => TryScalar(step, "id", out var id) && id == "checkout-candidate-data");
        var with = Mapping(candidateCheckout, "with");
        Assert.Equal("docs/develop/theory", Scalar(with, "sparse-checkout"));
        Assert.Equal("false", Scalar(with, "persist-credentials"));
    }

    [Fact]
    public void WritebackAuthorizationRequiresByteIdenticalTrustedRecomputation()
    {
        var script = LoadScript();

        Assert.Contains(
            "cmp -s -- \"$proposal_patch\" \"$trusted_patch\"",
            script,
            StringComparison.Ordinal);
        Assert.Contains(
            "authorize_exact_patch \"$proposal_patch\" \"$recomputed_patch\"",
            script,
            StringComparison.Ordinal);
        Assert.Contains("THEORY-INGEST-CLOSURE-001", script, StringComparison.Ordinal);
    }

    [Fact]
    public void WritebackAuthorizedPathsAreDerivedFromFileMap()
    {
        var script = LoadScript();

        Assert.Contains(
            "filemap-conform --producer-write-set IngestCommand",
            script,
            StringComparison.Ordinal);
        Assert.Contains("load_producer_write_patterns", script, StringComparison.Ordinal);
        Assert.DoesNotContain("Meta/Digestion/atoms/**", script, StringComparison.Ordinal);
        Assert.DoesNotContain("Meta/Digestion/backfill/**", script, StringComparison.Ordinal);
    }

    [Fact]
    public void WritebackFailsClosedWhenCandidateChangesProducerClosure()
    {
        var script = LoadScript();

        Assert.Contains(
            "assert_producer_closure_unchanged \"$repository\" \"$base_sha\" \"$head_sha\"",
            script,
            StringComparison.Ordinal);
        Assert.Contains("Makefile", script, StringComparison.Ordinal);
        Assert.Contains("tools/StrataLint.*", script, StringComparison.Ordinal);
        Assert.Contains("tools/scripts/*", script, StringComparison.Ordinal);
        Assert.Contains("Meta/FILEMAP.toml", script, StringComparison.Ordinal);
        Assert.Contains(WorkflowPath, script, StringComparison.Ordinal);
        Assert.Contains("THEORY-INGEST-CLOSURE-001", script, StringComparison.Ordinal);
    }

    [Fact]
    public void WriteTransactionPinsEventHeadAndUsesExpectedOldShaLeaseWithoutForceUpdate()
    {
        var workflow = Render(Job(LoadWorkflow(), "writeback"));
        var script = LoadScript();

        Assert.Contains("github.event.pull_request.head.sha", workflow, StringComparison.Ordinal);
        Assert.Contains("github.event.pull_request.head.ref", workflow, StringComparison.Ordinal);
        Assert.Contains("github.event.pull_request.head.repo.full_name", workflow, StringComparison.Ordinal);
        Assert.Contains("github.repository", workflow, StringComparison.Ordinal);
        Assert.Contains("--force-with-lease=\"$remote_ref:$head_sha\"", script, StringComparison.Ordinal);
        Assert.Contains("\"$commit_sha:$remote_ref\"", script, StringComparison.Ordinal);
        Assert.Contains(
            "merge-base --is-ancestor \"$head_sha\" \"$commit_sha\"",
            script,
            StringComparison.Ordinal);
        Assert.DoesNotContain("--force \"", script, StringComparison.Ordinal);
        Assert.DoesNotContain("+$commit_sha", script, StringComparison.Ordinal);
    }

    private static YamlMappingNode LoadWorkflow()
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create(".github/workflows/theory-ingest.yml"))));
        return Assert.IsType<YamlMappingNode>(Assert.Single(stream.Documents).RootNode);
    }

    private static string LoadScript() => TestRepositoryLayout.ReadAllText(
        RepositoryRelativePath.Create("tools/scripts/workflow/theory-ingest-closure.sh"));

    private static YamlMappingNode Job(YamlMappingNode workflow, string name) =>
        Mapping(Mapping(workflow, "jobs"), name);

    private static YamlMappingNode Mapping(YamlMappingNode node, string key) =>
        Assert.IsType<YamlMappingNode>(node.Children[new YamlScalarNode(key)]);

    private static YamlSequenceNode Sequence(YamlMappingNode node, string key) =>
        Assert.IsType<YamlSequenceNode>(node.Children[new YamlScalarNode(key)]);

    private static string Scalar(YamlMappingNode node, string key) =>
        Assert.IsType<YamlScalarNode>(node.Children[new YamlScalarNode(key)]).Value ?? string.Empty;

    private static bool TryScalar(YamlMappingNode node, string key, out string value)
    {
        if (node.Children.TryGetValue(new YamlScalarNode(key), out var child)
            && child is YamlScalarNode { Value: { } scalar })
        {
            value = scalar;
            return true;
        }

        value = string.Empty;
        return false;
    }

    private static IEnumerable<string> DescendantScalars(YamlNode node) => node switch
    {
        YamlScalarNode { Value: { } value } => [value],
        YamlSequenceNode sequence => sequence.Children.SelectMany(DescendantScalars),
        YamlMappingNode mapping => mapping.Children
            .SelectMany(static pair => DescendantScalars(pair.Key).Concat(DescendantScalars(pair.Value))),
        _ => [],
    };

    private static string Render(YamlNode node)
    {
        var stream = new YamlStream(new YamlDocument(node));
        using var writer = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        stream.Save(writer, assignAnchors: false);
        return writer.ToString();
    }
}
