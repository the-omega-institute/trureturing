using YamlDotNet.RepresentationModel;

namespace StrataLint.Tests;

public sealed partial class AdmissionWorkflowTests
{
    [Fact]
    public void EveryPullRequestMergeCheckoutIsImmediatelyPrecededByMergeRefWait()
    {
        const string mergeRefExpression = "format('refs/pull/{0}/merge', github.event.pull_request.number)";
        const string expectedWaitCondition = "github.event_name == 'pull_request_target'";
        var mergeCheckoutCount = 0;

        foreach (var (jobNameNode, jobNode) in Jobs(SharedAdmissionWorkflow).Children)
        {
            if (jobNameNode is not YamlScalarNode { Value: not null } jobName
                || jobNode is not YamlMappingNode job
                || !job.Children.TryGetValue(new YamlScalarNode("steps"), out var stepsNode)
                || stepsNode is not YamlSequenceNode stepSequence)
                continue;

            var steps = stepSequence.Children.OfType<YamlMappingNode>().ToArray();
            for (var index = 0; index < steps.Length; index++)
            {
                var checkout = steps[index];
                if (!checkout.Children.TryGetValue(new YamlScalarNode("uses"), out var usesNode)
                    || usesNode is not YamlScalarNode { Value: "actions/checkout@v4" }
                    || !checkout.Children.TryGetValue(new YamlScalarNode("with"), out var withNode)
                    || withNode is not YamlMappingNode with
                    || !with.Children.TryGetValue(new YamlScalarNode("ref"), out var refNode)
                    || refNode is not YamlScalarNode { Value: not null } checkoutRef
                    || !checkoutRef.Value.Contains(mergeRefExpression, StringComparison.Ordinal))
                    continue;

                mergeCheckoutCount++;
                Assert.True(index > 0, $"merge-ref checkout in job '{jobName.Value}' has no preceding step");
                var wait = steps[index - 1];
                Assert.Equal("Wait for the GitHub merge ref", StepName(wait));
                Assert.Equal(
                    expectedWaitCondition,
                    Assert.IsType<YamlScalarNode>(wait.Children[new YamlScalarNode("if")]).Value);
            }
        }

        Assert.Equal(3, mergeCheckoutCount);
    }
}
