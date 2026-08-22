using YamlDotNet.RepresentationModel;

namespace StrataLint.ArchitectureTests;

/// <summary>
/// The Lean build archive published to GitHub Releases is consumed as compiled .olean input,
/// so whoever can publish it sits underneath admission. Three seats reading independently
/// (#2729) established that a job-internal ref check is not a machine boundary: `gh workflow
/// run --ref` selects the workflow version from that branch, so a non-base version can delete
/// its own check. The boundary has to be the trigger set itself.
///
/// This pins the closure rather than any single file: exactly one workflow may hold
/// `contents: write`, and that workflow may only run on a schedule. A second writable
/// workflow, or a manual trigger added back to this one, turns this red instead of relying
/// on a reviewer remembering why it mattered.
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

    [Fact]
    public void OnlyTheArchivePublisherMayWriteRepositoryContents()
    {
        var writers = Workflows
            .Where(static source => DeclaresContentsWrite(source.Content))
            .Select(static source => source.Path)
            .ToArray();

        Assert.Equal([ArchivePublisher], writers);
    }

    [Fact]
    public void TheArchivePublisherRunsOnlyOnASchedule()
    {
        var publisher = Workflows.SingleOrDefault(static source => source.Path == ArchivePublisher);
        Assert.NotNull(publisher);

        Assert.Equal(["schedule"], TriggerNames(publisher.Content));
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
