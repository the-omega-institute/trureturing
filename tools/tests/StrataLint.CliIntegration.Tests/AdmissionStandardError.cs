using System.Text;
using System.Text.Json;

namespace StrataLint.CliIntegration.Tests;

internal static class AdmissionStandardError
{
    internal static void AssertOnlyTimingEvents(byte[] standardError)
    {
        using var lines = new StringReader(Encoding.UTF8.GetString(standardError));
        while (lines.ReadLine() is { } line)
        {
            Assert.True(IsTimingEvent(line), $"Unexpected admission stderr: {line}");
        }
    }

    private static bool IsTimingEvent(string line)
    {
        try
        {
            using var document = JsonDocument.Parse(line);
            var root = document.RootElement;
            return root.ValueKind == JsonValueKind.Object
                && root.EnumerateObject().Count() == 6
                && ReadString(root, "event") == "gate_stage_timing"
                && ReadString(root, "level") == "information"
                && ReadString(root, "scope") == "admission-check"
                && !string.IsNullOrWhiteSpace(ReadString(root, "stage"))
                && ReadString(root, "status") is "passed" or "failed"
                && root.TryGetProperty("elapsed_seconds", out var elapsed)
                && elapsed.ValueKind == JsonValueKind.Number
                && elapsed.TryGetDouble(out var seconds)
                && double.IsFinite(seconds)
                && seconds >= 1;
        }
        catch (JsonException)
        {
            return false;
        }
    }

    private static string? ReadString(JsonElement root, string property) =>
        root.TryGetProperty(property, out var value) && value.ValueKind == JsonValueKind.String
            ? value.GetString()
            : null;
}
