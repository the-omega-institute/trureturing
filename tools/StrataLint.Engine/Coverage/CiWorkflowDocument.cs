using System.Collections.Immutable;
using YamlDotNet.Core;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Engine;

internal sealed record CiWorkflowJob(string Name, string? Uses);

// Consumers inspect workflow data; this parser makes no claim that Actions executed a job.
internal sealed class CiWorkflowDocument(
    YamlMappingNode root,
    ImmutableDictionary<string, CiWorkflowJob> jobs)
{
    internal const string DeltaJobName = "delta";
    internal const string PushCallName = "push";
    internal ImmutableDictionary<string, CiWorkflowJob> Jobs => jobs;

    internal static CiWorkflowDocument? Parse(string text)
    {
        try
        {
            var yaml = new YamlStream();
            yaml.Load(new StringReader(text));
            if (yaml.Documents.Count != 1
                || yaml.Documents[0].RootNode is not YamlMappingNode root
                || Child(root, "jobs") is not YamlMappingNode jobs)
            {
                return null;
            }

            var parsed = ImmutableDictionary.CreateBuilder<string, CiWorkflowJob>(StringComparer.Ordinal);
            foreach (var (key, value) in jobs.Children)
            {
                if (key is not YamlScalarNode { Value: { Length: > 0 } id }
                    || value is not YamlMappingNode job)
                {
                    return null;
                }

                var name = Child(job, "name");
                var uses = Child(job, "uses");
                if (name is not null and not YamlScalarNode { Value.Length: > 0 }
                    || uses is not null and not YamlScalarNode { Value.Length: > 0 })
                {
                    return null;
                }

                parsed.Add(id, new CiWorkflowJob(
                    (name as YamlScalarNode)?.Value ?? id,
                    (uses as YamlScalarNode)?.Value));
            }

            return new CiWorkflowDocument(root, parsed.ToImmutable());
        }
        catch (Exception exception) when (exception is YamlException or ArgumentException or InvalidOperationException)
        {
            return null;
        }
    }

    internal bool HasEvent(string name) => Child(root, "on") switch
    {
        YamlMappingNode triggers => Child(triggers, name) is not null,
        YamlScalarNode scalar => scalar.Value == name,
        YamlSequenceNode sequence => sequence.Children.OfType<YamlScalarNode>().Any(item => item.Value == name),
        _ => false,
    };

    internal bool RunsOnBranch(string name, string branch) =>
        Child(root, "on") is YamlMappingNode triggers
        && Child(triggers, name) is YamlMappingNode trigger
        && Child(trigger, "branches") is YamlSequenceNode branches
        && branches.Children.OfType<YamlScalarNode>().Any(item => item.Value == branch);

    internal bool HasDeltaGate(string branch) =>
        RunsOnBranch("pull_request_target", branch)
        && Jobs.TryGetValue(DeltaJobName, out var job)
        && job is { Name: DeltaJobName, Uses: null };

    private static YamlNode? Child(YamlMappingNode node, string key) =>
        node.Children.TryGetValue(new YamlScalarNode(key), out var value) ? value : null;
}
