using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    private static IReadOnlyList<JsonElement> ReadItems(string output) =>
        ReadEvents(output, "clean_lanes_item");

    private static JsonElement ReadSummary(string output) =>
        Assert.Single(ReadEvents(output, "clean_lanes_summary"));

    private static IReadOnlyList<JsonElement> ReadEvents(string output, string eventName)
    {
        var events = new List<JsonElement>();
        foreach (var line in output.Split('\n', StringSplitOptions.RemoveEmptyEntries))
        {
            using var document = JsonDocument.Parse(line);
            if (document.RootElement.GetProperty("event").GetString() == eventName)
            {
                events.Add(document.RootElement.Clone());
            }
        }

        return events;
    }

    private static void AssertItemProperty(
        IReadOnlyList<JsonElement> items,
        string selectorProperty,
        string selectorValue,
        string property,
        string expected)
    {
        var item = items.Single(candidate =>
            candidate.GetProperty(selectorProperty).GetString() == selectorValue);
        Assert.Equal(expected, item.GetProperty(property).GetString());
    }

    private static void AssertGhInvocation(
        IReadOnlyList<WorktreeProcessInvocation> invocations,
        string branch,
        string workingDirectory)
    {
        var invocation = Assert.Single(
            invocations,
            static candidate => candidate.FileName == "gh");
        AssertProbeInvocation(
            invocation,
            "gh",
            [
                "pr", "list", "--state", "all", "--head", branch,
                "--json", "state,headRefName,headRefOid,mergeCommit", "--limit", "100",
            ],
            workingDirectory);
    }

    private static void AssertLsofInvocations(
        IReadOnlyList<WorktreeProcessInvocation> invocations,
        int expectedCount)
    {
        var probes = invocations
            .Where(static candidate => candidate.FileName == "lsof")
            .ToArray();
        Assert.Equal(expectedCount, probes.Length);
        Assert.All(probes, static invocation =>
            AssertProbeInvocation(
                invocation,
                "lsof",
                ["-nP", "-F0pfn"],
                Path.GetTempPath()));
    }

    private static void AssertProbeInvocation(
        WorktreeProcessInvocation invocation,
        string fileName,
        string[] expectedArguments,
        string workingDirectory)
    {
        Assert.Equal(fileName, invocation.FileName);
        Assert.Equal(expectedArguments, invocation.Arguments.ToArray());
        Assert.Equal(workingDirectory, invocation.WorkingDirectory);
        Assert.Equal(BoundedProcessRunner.HangDetectionBudget, invocation.Timeout);
    }

    private static bool ItemMatches(
        JsonElement item,
        string path,
        string action,
        string reason) =>
        item.GetProperty("path").GetString() == path
        && item.GetProperty("action").GetString() == action
        && item.GetProperty("reason").GetString() == reason;

    private static string ReasonFor(string output, string path) =>
        ReadItems(output)
            .Single(item => item.GetProperty("path").GetString() == path)
            .GetProperty("reason")
            .GetString()!;
}
