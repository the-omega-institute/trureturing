using System.Text.RegularExpressions;
using YamlDotNet.RepresentationModel;

namespace StrataLint.Tests;

internal static class CandidateEngineeringReachabilityWitness
{
    internal sealed record Result(bool IsReachable, string Reason);

    private enum ConditionState
    {
        Enabled,
        Skipped,
        Undecidable
    }

    internal static Result Check(string workflow)
    {
        var root = ParseRoot(workflow);
        if (!root.Children.TryGetValue(new YamlScalarNode("jobs"), out var jobsNode)
            || jobsNode is not YamlMappingNode jobs)
        {
            return new Result(false, "workflow has no jobs mapping");
        }

        var events = ConfiguredEvents(root);
        if (events.Length == 0)
        {
            return new Result(false, "workflow has no configured events");
        }

        foreach (var eventName in events)
        {
            var result = Reachable(
                jobs,
                "candidate-engineering",
                eventName,
                [],
                new Dictionary<string, Result>(StringComparer.Ordinal));
            if (!result.IsReachable) return result;
        }

        return new Result(true, "candidate-engineering is reachable for every configured event");
    }

    private static YamlMappingNode ParseRoot(string workflow)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        return Assert.IsType<YamlMappingNode>(stream.Documents.Single().RootNode);
    }

    private static string[] ConfiguredEvents(YamlMappingNode root)
    {
        if (!root.Children.TryGetValue(new YamlScalarNode("on"), out var trigger)) return [];
        return trigger switch
        {
            YamlScalarNode scalar when !string.IsNullOrWhiteSpace(scalar.Value) => [scalar.Value!],
            YamlSequenceNode sequence => sequence.Children
                .OfType<YamlScalarNode>()
                .Select(node => node.Value)
                .Where(value => !string.IsNullOrWhiteSpace(value))
                .Select(value => value!)
                .Distinct(StringComparer.Ordinal)
                .ToArray(),
            YamlMappingNode mapping => mapping.Children.Keys
                .OfType<YamlScalarNode>()
                .Select(node => node.Value)
                .Where(value => !string.IsNullOrWhiteSpace(value))
                .Select(value => value!)
                .Distinct(StringComparer.Ordinal)
                .ToArray(),
            _ => []
        };
    }

    private static Result Reachable(
        YamlMappingNode jobs,
        string jobName,
        string eventName,
        IReadOnlyList<string> path,
        IDictionary<string, Result> memo)
    {
        if (memo.TryGetValue(jobName, out var cached)) return cached;
        if (path.Contains(jobName, StringComparer.Ordinal))
        {
            return new Result(false, $"{FormatPath(path, jobName)}: dependency cycle");
        }
        if (!jobs.Children.TryGetValue(new YamlScalarNode(jobName), out var node)
            || node is not YamlMappingNode job)
        {
            return new Result(false, $"{FormatPath(path, jobName)}: missing job");
        }

        var condition = EvaluateJobCondition(Scalar(job, "if"), eventName);
        if (condition != ConditionState.Enabled)
        {
            var detail = condition == ConditionState.Skipped ? "condition excludes" : "condition is undecidable";
            var result = new Result(false, $"{FormatPath(path, jobName)}: {detail} event '{eventName}'");
            memo[jobName] = result;
            return result;
        }

        if (!TryNeeds(job, out var needs, out var needsError))
        {
            var result = new Result(false, $"{FormatPath(path, jobName)}: {needsError}");
            memo[jobName] = result;
            return result;
        }

        var nextPath = path.Append(jobName).ToArray();
        foreach (var need in needs)
        {
            var result = Reachable(jobs, need, eventName, nextPath, memo);
            if (!result.IsReachable)
            {
                memo[jobName] = result;
                return result;
            }
        }

        var reachable = new Result(true, $"{FormatPath(path, jobName)}: reachable");
        memo[jobName] = reachable;
        return reachable;
    }

    private static bool TryNeeds(YamlMappingNode job, out string[] needs, out string error)
    {
        needs = [];
        error = string.Empty;
        if (!job.Children.TryGetValue(new YamlScalarNode("needs"), out var value)) return true;
        if (value is YamlScalarNode scalar && !string.IsNullOrWhiteSpace(scalar.Value))
        {
            needs = [scalar.Value!];
            return true;
        }
        if (value is YamlSequenceNode sequence)
        {
            var entries = sequence.Children.OfType<YamlScalarNode>().Select(node => node.Value).ToArray();
            if (entries.All(value => !string.IsNullOrWhiteSpace(value)))
            {
                needs = entries.Select(value => value!).Distinct(StringComparer.Ordinal).ToArray();
                return true;
            }
        }
        error = "needs is not a non-empty job id or sequence of job ids";
        return false;
    }

    private static ConditionState EvaluateJobCondition(string condition, string eventName)
    {
        var expression = condition.Trim();
        if (expression.StartsWith("${{", StringComparison.Ordinal)
            && expression.EndsWith("}}", StringComparison.Ordinal))
        {
            expression = expression[3..^2].Trim();
        }
        if (expression is "" or "true" or "always()") return ConditionState.Enabled;
        if (expression == "false") return ConditionState.Skipped;
        if (expression == "success()") return ConditionState.Undecidable;

        var equality = Regex.Match(
            expression,
            "^github\\.event_name\\s*(?<operator>==|!=)\\s*'(?<event>[^']+)'$",
            RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);
        if (!equality.Success)
        {
            equality = Regex.Match(
                expression,
                "^github\\.event_name\\s*(?<operator>==|!=)\\s*\"(?<event>[^\"]+)\"$",
                RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);
        }
        if (!equality.Success) return ConditionState.Undecidable;

        var equal = string.Equals(equality.Groups["event"].Value, eventName, StringComparison.Ordinal);
        if (equality.Groups["operator"].Value == "!=") equal = !equal;
        return equal ? ConditionState.Enabled : ConditionState.Skipped;
    }

    private static string FormatPath(IReadOnlyList<string> path, string current) =>
        string.Join(" -> ", path.Append(current));

    private static string Scalar(YamlMappingNode node, string key) =>
        node.Children.TryGetValue(new YamlScalarNode(key), out var value)
            ? ((YamlScalarNode)value).Value ?? string.Empty
            : string.Empty;
}
