using System.Text.Json;

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
