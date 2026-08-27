using StrataLint.Engine;
using YamlDotNet.RepresentationModel;
using System.Text.RegularExpressions;

namespace StrataLint.Tests;

public sealed partial class AdmissionWorkflowTests
{
    private static void WriteFloorProject(string repository, string assembly, string className)
    {
        var directory = Path.Combine(repository, "tools", "tests", assembly);
        Directory.CreateDirectory(directory);
        File.WriteAllText(
            Path.Combine(directory, $"{assembly}.csproj"),
            $"""
            <Project Sdk="Microsoft.NET.Sdk">
              <PropertyGroup><TargetFramework>net10.0</TargetFramework><IsTestProject>true</IsTestProject><AssemblyName>{assembly}</AssemblyName><RestorePackagesWithLockFile>false</RestorePackagesWithLockFile></PropertyGroup>
              <ItemGroup><PackageReference Include="Microsoft.NET.Test.Sdk" Version="18.0.1" /><PackageReference Include="xunit" Version="2.9.3" /><PackageReference Include="xunit.runner.visualstudio" Version="3.1.4" /></ItemGroup>
            </Project>
            """);
        File.WriteAllText(
            Path.Combine(directory, "FloorProbe.cs"),
            $"using System; using System.IO; using Xunit; public sealed class {className} {{ [Fact] public void Runs() => File.AppendAllText(Environment.GetEnvironmentVariable(\"ENGINEERING_FLOOR_MARKER\")!, \"{assembly}\\n\"); }}\n");
    }

    private static string StepScript(IEnumerable<YamlMappingNode> steps, string name)
    {
        var step = Assert.Single(steps, candidate => StepName(candidate) == name);
        return Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("run")]).Value
            ?? string.Empty;
    }

    private static ProcessOutput RunEngineeringScope(
        string engineeringRoot,
        string repositoryRoot,
        string planFile,
        string head,
        string @base,
        params string[] environment) =>
        RunEngineeringScopeMode(engineeringRoot, repositoryRoot, planFile, head, @base, "execute", environment);

    private static ProcessOutput RunEngineeringScopeMode(
        string engineeringRoot,
        string repositoryRoot,
        string planFile,
        string head,
        string @base,
        string mode,
        params string[] environment)
    {
        var project = Path.Combine(
            engineeringRoot,
            "tools",
            "StrataLint.EngineeringScope",
            "StrataLint.EngineeringScope.csproj");
        var build = BoundedProcessRunner.Run(
            DotnetHost(engineeringRoot),
            ["build", project, "--configuration", "Release", "--no-restore", "--nologo"],
            engineeringRoot,
            TimeSpan.FromMinutes(2),
            2 * 1024 * 1024);
        Assert.True(
            build.ExitCode == 0,
            System.Text.Encoding.UTF8.GetString(build.StandardOutput)
                + System.Text.Encoding.UTF8.GetString(build.StandardError));
        var arguments = new List<string>(environment)
        {
            DotnetHost(engineeringRoot),
            "run",
            "--project",
            project,
            "--configuration",
            "Release",
            "--no-launch-profile",
            "--no-build",
            "--no-restore",
            "--",
            "--mode",
            mode,
            "--repository",
            repositoryRoot,
            "--head",
            head,
            "--base",
            @base,
            "--plan-file",
            planFile,
        };
        return BoundedProcessRunner.Run(
            "env",
            arguments,
            repositoryRoot,
            TimeSpan.FromMinutes(2),
            2 * 1024 * 1024);
    }

    private static string DotnetHost(string root)
    {
        var result = BoundedProcessRunner.Run(
            "/bin/sh",
            ["-c", "command -v dotnet"],
            root,
            TimeSpan.FromSeconds(10),
            4096);
        Assert.Equal(0, result.ExitCode);
        return System.Text.Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    private static string GitText(string repository, params string[] arguments)
    {
        var result = BoundedProcessRunner.Run(
            "git",
            ["-C", repository, .. arguments],
            repository,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);
        Assert.Equal(0, result.ExitCode);
        return System.Text.Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    private static void Git(string repository, params string[] arguments) =>
        _ = GitText(repository, arguments);

    private static void WriteExecutable(string path, string content)
    {
        File.WriteAllText(path, content);
        if (OperatingSystem.IsWindows()) return;
        File.SetUnixFileMode(
            path,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }

    private static string ReadTemporaryText(string path)
    {
        using var reader = new StreamReader(path);
        return reader.ReadToEnd();
    }

    private static string JobText(string workflow, string job, string nextJob)
    {
        var start = workflow.IndexOf($"  {job}:\n", StringComparison.Ordinal);
        var end = workflow.IndexOf($"  {nextJob}:\n", start, StringComparison.Ordinal);
        Assert.True(start >= 0 && end > start);
        return workflow[start..end];
    }

    private static string AdmissionWorkflow() =>
        File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), ".github", "workflows", "ci.yml"));

    private static YamlMappingNode Jobs(string workflow)
    {
        var stream = new YamlStream();
        stream.Load(new StringReader(workflow));
        var document = Assert.IsType<YamlMappingNode>(stream.Documents[0].RootNode);
        return Assert.IsType<YamlMappingNode>(document.Children[new YamlScalarNode("jobs")]);
    }

    private static YamlMappingNode Job(string workflow, string job) =>
        Assert.IsType<YamlMappingNode>(Jobs(workflow).Children[new YamlScalarNode(job)]);

    private static YamlMappingNode[] JobSteps(string workflow, string job) =>
        Assert.IsType<YamlSequenceNode>(Job(workflow, job).Children[new YamlScalarNode("steps")])
            .Children
            .OfType<YamlMappingNode>()
            .ToArray();

    private static string StepName(YamlMappingNode step) =>
        Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("name")]).Value ?? string.Empty;

    private static bool ContainsDotnetInvocation(string script) =>
        MaskSingleQuotedLiterals(script).Contains("dotnet", StringComparison.Ordinal);

    private static string MaskSingleQuotedLiterals(string script)
    {
        var characters = script.ToCharArray();
        var singleQuoteStart = -1;
        var inDoubleQuote = false;
        var escaped = false;
        for (var index = 0; index < characters.Length; index++)
        {
            var character = characters[index];
            if (singleQuoteStart >= 0)
            {
                if (character != '\'') continue;

                Array.Fill(characters, ' ', singleQuoteStart, index - singleQuoteStart + 1);
                singleQuoteStart = -1;
                continue;
            }

            if (escaped)
            {
                escaped = false;
                continue;
            }

            if (character == '\\')
            {
                escaped = true;
                continue;
            }

            if (character == '"')
            {
                inDoubleQuote = !inDoubleQuote;
                continue;
            }

            if (!inDoubleQuote && character == '\'') singleQuoteStart = index;
        }

        return new string(characters);
    }

    private static bool BaselineNeedsExactlyLeanInspect(string workflow) =>
        Needs(Job(workflow, "baseline-admission")).SequenceEqual(["lean-inspect"], StringComparer.Ordinal);

    private static IEnumerable<string> Needs(YamlMappingNode job)
    {
        if (!job.Children.TryGetValue(new YamlScalarNode("needs"), out var needs)) yield break;
        if (needs is YamlScalarNode scalar)
        {
            yield return scalar.Value!;
            yield break;
        }
        foreach (var item in Assert.IsType<YamlSequenceNode>(needs).Children.OfType<YamlScalarNode>())
            yield return item.Value!;
    }

    private static string BaselineResolutionScript(string workflow)
    {
        var leanInspect = Assert.IsType<YamlMappingNode>(
            Jobs(workflow).Children[new YamlScalarNode("lean-inspect")]);
        var steps = Assert.IsType<YamlSequenceNode>(
            leanInspect.Children[new YamlScalarNode("steps")]);
        var step = Assert.Single(
            steps.Children.OfType<YamlMappingNode>(),
            node => node.Children.TryGetValue(new YamlScalarNode("id"), out var id)
                && id is YamlScalarNode { Value: "base" });
        return Assert.IsType<YamlScalarNode>(step.Children[new YamlScalarNode("run")]).Value ?? string.Empty;
    }
}

public sealed class CandidateEngineeringReachabilityTests
{
    [Fact]
    public void CandidateEngineeringAndEveryTransitiveNeedAreReachableForEveryConfiguredEvent()
    {
        var result = CandidateEngineeringReachabilityWitness.Check(
            AdmissionWorkflowReachabilityFixture.Workflow);

        Assert.True(result.IsReachable, result.Reason);
    }

    [Fact]
    public void ReachabilityRejectsJobConditionThatExcludesAConfiguredEvent()
    {
        const string workflow = """
            on: push
            jobs:
              candidate-engineering:
                if: false
            """;

        var result = CandidateEngineeringReachabilityWitness.Check(workflow);

        Assert.False(result.IsReachable);
        Assert.Contains("candidate-engineering", result.Reason, StringComparison.Ordinal);
        Assert.Contains("event 'push'", result.Reason, StringComparison.Ordinal);
    }

    [Fact]
    public void ReachabilityFollowsEveryTransitiveNeed()
    {
        const string workflow = """
            on:
              push:
              pull_request_target:
            jobs:
              skipped-root:
                if: github.event_name == 'workflow_dispatch'
              middle:
                needs: skipped-root
              candidate-engineering:
                needs: middle
            """;

        var result = CandidateEngineeringReachabilityWitness.Check(workflow);

        Assert.False(result.IsReachable);
        Assert.Contains(
            "candidate-engineering -> middle -> skipped-root",
            result.Reason,
            StringComparison.Ordinal);
        Assert.Contains("event 'push'", result.Reason, StringComparison.Ordinal);
    }

    [Fact]
    public void ReachabilityFailsClosedForUndecidablePredecessorCondition()
    {
        const string workflow = """
            on: push
            jobs:
              guarded:
                if: github.actor == 'octocat'
              candidate-engineering:
                needs: guarded
            """;

        var result = CandidateEngineeringReachabilityWitness.Check(workflow);

        Assert.False(result.IsReachable);
        Assert.Contains("candidate-engineering -> guarded", result.Reason, StringComparison.Ordinal);
        Assert.Contains("undecidable", result.Reason, StringComparison.Ordinal);
    }

    [Fact]
    public void ReachabilityChecksEveryConfiguredEvent()
    {
        const string workflow = """
            on: [push, pull_request_target]
            jobs:
              push-only:
                if: github.event_name == 'push'
              candidate-engineering:
                needs: push-only
            """;

        var result = CandidateEngineeringReachabilityWitness.Check(workflow);

        Assert.False(result.IsReachable);
        Assert.Contains("event 'pull_request_target'", result.Reason, StringComparison.Ordinal);
    }

    [Fact]
    public void ReachabilityAllowsOrdinaryUnrelatedAndStepNameEditsWithAReachableNeed()
    {
        const string workflow = """
            on: [push, pull_request_target]
            jobs:
              unrelated:
                if: github.actor == 'octocat'
              reachable-prerequisite:
                steps:
                  - name: A renamed step is not topology
                    run: "true"
              candidate-engineering:
                needs: reachable-prerequisite
                steps:
                  - name: Another harmless rename
                    run: "true"
            """;

        var result = CandidateEngineeringReachabilityWitness.Check(workflow);

        Assert.True(result.IsReachable, result.Reason);
    }
}

internal static class AdmissionWorkflowReachabilityFixture
{
    internal static string Workflow => File.ReadAllText(Path.Combine(
        TestRepositoryLayout.FindRoot(), ".github", "workflows", "ci.yml"));
}

internal static class CandidateEngineeringReachabilityWitness
{
    internal sealed record Result(bool IsReachable, string Reason);

    private enum ConditionState
    {
        Enabled,
        Skipped,
        Undecidable,
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
            YamlSequenceNode sequence => EventNames(sequence.Children),
            YamlMappingNode mapping => EventNames(mapping.Children.Keys),
            _ => [],
        };
    }

    private static string[] EventNames(IEnumerable<YamlNode> nodes) => nodes
        .OfType<YamlScalarNode>()
        .Select(static node => node.Value)
        .Where(static value => !string.IsNullOrWhiteSpace(value))
        .Select(static value => value!)
        .Distinct(StringComparer.Ordinal)
        .ToArray();

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

        var conditionText = Scalar(job, "if");
        var condition = EvaluateJobCondition(conditionText, eventName);
        if (condition != ConditionState.Enabled)
        {
            var detail = condition == ConditionState.Skipped
                ? $"condition '{conditionText}' excludes"
                : $"condition '{conditionText}' is undecidable for";
            var result = new Result(
                false,
                $"{FormatPath(path, jobName)}: {detail} event '{eventName}'");
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
            var entries = sequence.Children.OfType<YamlScalarNode>().Select(static node => node.Value).ToArray();
            if (entries.Length == sequence.Children.Count
                && entries.All(static entry => !string.IsNullOrWhiteSpace(entry)))
            {
                needs = entries.Select(static entry => entry!).Distinct(StringComparer.Ordinal).ToArray();
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
        && value is YamlScalarNode scalar
            ? scalar.Value ?? string.Empty
            : string.Empty;
}
