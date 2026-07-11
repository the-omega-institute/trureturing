using System.Text;
using YamlDotNet.Core;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Cli;

internal abstract record AdmissionTopologyOutcome
{
    private AdmissionTopologyOutcome() { }

    internal sealed record BootstrapNotActive(string DefaultBranch) : AdmissionTopologyOutcome;

    internal sealed record SteadyStateActive(string DefaultBranch) : AdmissionTopologyOutcome;

    internal sealed record InfrastructureFailure(string Message) : AdmissionTopologyOutcome;
}

internal static class AdmissionWorkflowTopology
{
    internal const string WorkflowPath = ".github/workflows/ci.yml";

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static bool HasRequiredBaseGate(ReadOnlySpan<byte> bytes, string defaultBranch)
    {
        try
        {
            var yaml = new YamlStream();
            using var reader = new StringReader(StrictUtf8.GetString(bytes));
            yaml.Load(reader);
            if (yaml.Documents.Count != 1
                || yaml.Documents[0].RootNode is not YamlMappingNode root
                || Child(root, "on") is not YamlMappingNode triggers
                || Child(triggers, "pull_request_target") is not YamlMappingNode pullRequestTarget
                || Child(pullRequestTarget, "branches") is not YamlSequenceNode branches
                || !branches.Children
                    .OfType<YamlScalarNode>()
                    .Any(branch => string.Equals(branch.Value, defaultBranch, StringComparison.Ordinal))
                || Child(root, "jobs") is not YamlMappingNode jobs
                || Child(jobs, "baseline-admission") is not YamlMappingNode)
            {
                return false;
            }

            return true;
        }
        catch (DecoderFallbackException)
        {
            return false;
        }
        catch (YamlException)
        {
            return false;
        }
    }

    private static YamlNode? Child(YamlMappingNode mapping, string key)
    {
        foreach (var pair in mapping.Children)
        {
            if (pair.Key is YamlScalarNode scalar
                && string.Equals(scalar.Value, key, StringComparison.Ordinal))
            {
                return pair.Value;
            }
        }

        return null;
    }
}
