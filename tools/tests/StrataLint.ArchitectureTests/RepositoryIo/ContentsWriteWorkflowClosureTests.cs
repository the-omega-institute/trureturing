using YamlDotNet.RepresentationModel;

namespace StrataLint.ArchitectureTests;

/// <summary>
/// The Lean build archive published to GitHub Releases is consumed as compiled .olean input,
/// so whoever can publish it sits underneath admission. Three seats reading independently
/// (#2729) established that a job-internal ref check is not a machine boundary: `gh workflow
/// run --ref` selects the workflow version from that branch, so a non-base version can delete
/// its own check. The boundary has to be the trigger set itself.
///
/// This pins the closure rather than any single file: the two explicitly authorized writers
/// are the scheduled Lean cache publisher and the dev-only truth-release publisher. A third
/// writable workflow, or an unapproved trigger added to either one, turns this red instead of
/// relying on a reviewer remembering why it mattered.
/// </summary>
public sealed class ContentsWriteWorkflowClosureTests
{
    private static readonly string RepositoryRoot = RepositoryLayout.FindRoot();

    private static readonly IReadOnlyList<WorkflowSource> Workflows =
        GitIndexRepositoryFiles.Enumerate(RepositoryRoot)
            .Where(static file => file.RelativePath.StartsWith(".github/workflows/", StringComparison.Ordinal)
                && (file.RelativePath.EndsWith(".yml", StringComparison.Ordinal)
                    || file.RelativePath.EndsWith(".yaml", StringComparison.Ordinal)))
            .OrderBy(static file => file.RelativePath, StringComparer.Ordinal)
            .Select(static file => new WorkflowSource(file.RelativePath, File.ReadAllText(file.FullPath)))
            .ToArray();

    private const string ArchivePublisher = ".github/workflows/lean-cache-publish.yml";
    private const string TruthReleasePublisher = ".github/workflows/truth-release-publish.yml";

    [Fact]
    public void OnlyTheAuthorizedPublishersMayWriteRepositoryContents()
    {
        var writers = Workflows
            .Where(static source => DeclaresContentsWrite(source.Content))
            .Select(static source => source.Path)
            .ToArray();

        Assert.Equal([ArchivePublisher, TruthReleasePublisher], writers);
    }

    [Fact]
    public void TheArchivePublisherRunsOnlyOnASchedule()
    {
        var publisher = Workflows.SingleOrDefault(static source => source.Path == ArchivePublisher);
        Assert.NotNull(publisher);

        Assert.Equal(["schedule"], TriggerNames(publisher.Content));
    }

    [Fact]
    public void TheTruthReleasePublisherRunsOnlyOnDevPush()
    {
        var publisher = Workflows.SingleOrDefault(static source => source.Path == TruthReleasePublisher);
        Assert.NotNull(publisher);

        Assert.Equal(["push"], TriggerNames(publisher.Content));
        Assert.Contains("branches: [dev]", publisher.Content, StringComparison.Ordinal);
        Assert.DoesNotContain("workflow_dispatch", publisher.Content, StringComparison.Ordinal);
        Assert.DoesNotContain("inputs.source_commit", publisher.Content, StringComparison.Ordinal);
    }

    [Fact]
    public void TheTruthReleasePublisherDerivesTrustOnlyFromTheProtectedDevTip()
    {
        var content = TruthReleaseWorkflow().Content;

        Assert.Contains("repos/${GITHUB_REPOSITORY}/branches/dev", content, StringComparison.Ordinal);
        Assert.Contains(".protected", content, StringComparison.Ordinal);
        Assert.Contains("the push SHA is no longer the current protected dev tip", content, StringComparison.Ordinal);
        Assert.Contains(".merge_base_commit.sha", content, StringComparison.Ordinal);
        Assert.Contains("commit_on_protected_dev=true", content, StringComparison.Ordinal);
        Assert.Contains("--commit-on-protected-dev \"$COMMIT_ON_PROTECTED_DEV\"", content, StringComparison.Ordinal);
        Assert.DoesNotContain("--commit-on-protected-dev true", content, StringComparison.Ordinal);
    }

    [Fact]
    public void TheTruthReleasePublisherSerializesAndBindsImmutableDigestPublications()
    {
        var content = TruthReleaseWorkflow().Content;

        Assert.Contains(
            "group: truth-release-publish-${{ needs.produce.outputs.release_digest }}",
            content,
            StringComparison.Ordinal);
        Assert.Contains("produced_at=\"$(date -u --date=\"@${commit_epoch}\"", content, StringComparison.Ordinal);
        Assert.Contains("--sort=name", content, StringComparison.Ordinal);
        Assert.Contains("gzip -n", content, StringComparison.Ordinal);
        Assert.Contains("oras pull \"$reference\"", content, StringComparison.Ordinal);
        Assert.Contains("cmp -s \"$ARCHIVE\"", content, StringComparison.Ordinal);
        Assert.Contains("immutable_reference=\"$OCI_REPOSITORY@$oci_digest\"", content, StringComparison.Ordinal);
        Assert.Contains("OCI lookup failed without a definitive not-found response", content, StringComparison.Ordinal);
        Assert.Contains("OCI digest tag moved during immutable verification", content, StringComparison.Ordinal);
        Assert.Contains(
            "source_url=\"https://github.com/${GITHUB_REPOSITORY}/commit/${SOURCE_COMMIT}\"",
            content,
            StringComparison.Ordinal);
        Assert.DoesNotContain(
            "org.opencontainers.image.source=https://github.com/${GITHUB_REPOSITORY}/commit/${GITHUB_SHA}",
            content,
            StringComparison.Ordinal);
    }

    [Fact]
    public void TheTruthReleaseProducerCannotPublishOrMintOidcCredentials()
    {
        var root = WorkflowRoot(TruthReleaseWorkflow());

        Assert.Empty(Permissions(root));
        Assert.Equal(
            new Dictionary<string, string>(StringComparer.Ordinal) { ["contents"] = "read" },
            Permissions(Job(root, "produce")));
        Assert.Equal(
            new Dictionary<string, string>(StringComparer.Ordinal)
            {
                ["contents"] = "write",
                ["packages"] = "write",
                ["id-token"] = "write",
                ["attestations"] = "write",
            },
            Permissions(Job(root, "publish")));
    }

    [Fact]
    public void TheTruthReleasePublisherConsumesOnlyTheRunBoundTransfer()
    {
        var content = TruthReleaseWorkflow().Content;
        var publisherScalars = ScalarValues(Job(WorkflowRoot(TruthReleaseWorkflow()), "publish"));

        Assert.Contains("artifact-ids: ${{ needs.produce.outputs.artifact_id }}", content, StringComparison.Ordinal);
        Assert.Contains("truth-release-transfer.v1", content, StringComparison.Ordinal);
        Assert.Contains(".run_id == $ENV.GITHUB_RUN_ID", content, StringComparison.Ordinal);
        Assert.Contains(".run_attempt == $ENV.GITHUB_RUN_ATTEMPT", content, StringComparison.Ordinal);
        Assert.Contains(".release_digest == $ENV.RELEASE_DIGEST", content, StringComparison.Ordinal);
        Assert.DoesNotContain(publisherScalars, static value => value.Contains("actions/checkout", StringComparison.Ordinal));
        Assert.DoesNotContain(publisherScalars, static value => value.Contains("actions/setup-dotnet", StringComparison.Ordinal));
        Assert.DoesNotContain(publisherScalars, static value => value.Contains("dotnet ", StringComparison.Ordinal));
        Assert.DoesNotContain(publisherScalars, static value => value.Contains("lake ", StringComparison.Ordinal));
        Assert.DoesNotContain(publisherScalars, static value => value.Contains("make ", StringComparison.Ordinal));
        Assert.DoesNotContain(publisherScalars, static value => value.Contains("tools/", StringComparison.Ordinal));
    }

    [Fact]
    public void TheTruthReleasePublisherRepairsAndVerifiesProvenanceOnEveryRun()
    {
        var content = TruthReleaseWorkflow().Content;

        Assert.DoesNotContain("steps.oci.outputs.pushed", content, StringComparison.Ordinal);
        Assert.Contains("attestations/${encoded_digest}", content, StringComparison.Ordinal);
        Assert.Contains("gh attestation verify", content, StringComparison.Ordinal);
        Assert.Contains("--signer-workflow \"$GITHUB_REPOSITORY/.github/workflows/truth-release-publish.yml\"", content, StringComparison.Ordinal);
        Assert.Contains("--source-digest \"$SOURCE_COMMIT\"", content, StringComparison.Ordinal);
        Assert.Contains("--source-ref 'refs/heads/dev'", content, StringComparison.Ordinal);
        Assert.Contains("GHCR provenance did not become verifiable", content, StringComparison.Ordinal);
    }

    [Fact]
    public void TheTruthReleasePublisherCreatesAndRepairsOneImmutableRelease()
    {
        var content = TruthReleaseWorkflow().Content;

        Assert.Contains("gh release create", content, StringComparison.Ordinal);
        Assert.Contains("gh release upload", content, StringComparison.Ordinal);
        Assert.Contains("gh release download", content, StringComparison.Ordinal);
        Assert.Contains("cmp -s \"$asset\" \"$verify_dir/$name\"", content, StringComparison.Ordinal);
        Assert.Contains("count=\"$(jq --arg name", content, StringComparison.Ordinal);
        Assert.Contains("assets=verified", content, StringComparison.Ordinal);
        Assert.DoesNotContain("release_collection_api=", content, StringComparison.Ordinal);
    }

    [Fact]
    public void EveryWorkflowDeclaresItsTriggersAndPermissionsExplicitly()
    {
        // A workflow with no `permissions:` block inherits the repository default, which is
        // configured outside this repository and can therefore grant write without any diff
        // here. Reading the closure only works if every member declares what it takes.
        var undeclared = Workflows
            .Where(static source => !DeclaresAnyContentsPermission(source.Content)
                || TriggerNames(source.Content).Count == 0)
            .Select(static source => source.Path)
            .ToArray();

        Assert.Empty(undeclared);
    }

    private static bool DeclaresContentsWrite(string content) =>
        ContentsValues(content).Contains("write", StringComparer.Ordinal);

    private static WorkflowSource TruthReleaseWorkflow() =>
        Workflows.Single(static source => source.Path == TruthReleasePublisher);

    private static YamlMappingNode WorkflowRoot(WorkflowSource workflow) =>
        Assert.IsType<YamlMappingNode>(Assert.Single(Documents(workflow.Content)));

    private static YamlMappingNode Job(YamlMappingNode root, string name)
    {
        var jobs = Assert.IsType<YamlMappingNode>(MappingValue(root, "jobs"));
        return Assert.IsType<YamlMappingNode>(MappingValue(jobs, name));
    }

    private static IReadOnlyDictionary<string, string> Permissions(YamlMappingNode mapping)
    {
        var permissions = Assert.IsType<YamlMappingNode>(MappingValue(mapping, "permissions"));
        return permissions.Children
            .ToDictionary(
                static pair => Assert.IsType<YamlScalarNode>(pair.Key).Value ?? string.Empty,
                static pair => Assert.IsType<YamlScalarNode>(pair.Value).Value ?? string.Empty,
                StringComparer.Ordinal);
    }

    private static YamlNode MappingValue(YamlMappingNode mapping, string key) =>
        mapping.Children.Single(pair =>
            pair.Key is YamlScalarNode scalar && string.Equals(scalar.Value, key, StringComparison.Ordinal)).Value;

    private static IReadOnlyList<string> ScalarValues(YamlNode root)
    {
        var values = new List<string>();
        Visit(root);
        return values;

        void Visit(YamlNode node)
        {
            switch (node)
            {
                case YamlScalarNode { Value: { } value }:
                    values.Add(value);
                    break;
                case YamlMappingNode mapping:
                    foreach (var (key, value) in mapping.Children)
                    {
                        Visit(key);
                        Visit(value);
                    }

                    break;
                case YamlSequenceNode sequence:
                    foreach (var item in sequence.Children) Visit(item);
                    break;
            }
        }
    }

    private static bool DeclaresAnyContentsPermission(string content) =>
        ContentsValues(content).Count > 0;

    private static IReadOnlyList<string> ContentsValues(string content)
    {
        var values = new List<string>();
        foreach (var node in Documents(content))
        {
            Walk(node, values);
        }

        return values;

        static void Walk(YamlNode node, List<string> values)
        {
            switch (node)
            {
                case YamlMappingNode mapping:
                    foreach (var (key, value) in mapping.Children)
                    {
                        if (key is YamlScalarNode { Value: "permissions" }
                            && value is YamlMappingNode permissions)
                        {
                            foreach (var (name, granted) in permissions.Children)
                            {
                                if (name is YamlScalarNode { Value: "contents" }
                                    && granted is YamlScalarNode { Value: { } grant })
                                {
                                    values.Add(grant);
                                }
                            }
                        }

                        Walk(value, values);
                    }

                    break;
                case YamlSequenceNode sequence:
                    foreach (var item in sequence.Children) Walk(item, values);
                    break;
            }
        }
    }

    private static IReadOnlyList<string> TriggerNames(string content)
    {
        foreach (var document in Documents(content))
        {
            if (document is not YamlMappingNode root) continue;
            foreach (var (key, value) in root.Children)
            {
                // YAML 1.1 reads a bare `on` as the boolean true, so both spellings appear.
                if (key is not YamlScalarNode { Value: "on" or "True" or "true" }) continue;
                return value switch
                {
                    YamlMappingNode mapping => mapping.Children.Keys
                        .OfType<YamlScalarNode>()
                        .Select(static scalar => scalar.Value ?? string.Empty)
                        .OrderBy(static name => name, StringComparer.Ordinal)
                        .ToArray(),
                    YamlSequenceNode sequence => sequence.Children
                        .OfType<YamlScalarNode>()
                        .Select(static scalar => scalar.Value ?? string.Empty)
                        .OrderBy(static name => name, StringComparer.Ordinal)
                        .ToArray(),
                    YamlScalarNode scalar => [scalar.Value ?? string.Empty],
                    _ => [],
                };
            }
        }

        return [];
    }

    private static IEnumerable<YamlNode> Documents(string content)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(content));
        return stream.Documents.Select(static document => document.RootNode).ToArray();
    }

    private sealed record WorkflowSource(string Path, string Content);
}
