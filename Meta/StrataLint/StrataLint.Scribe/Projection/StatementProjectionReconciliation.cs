using System.Text.Json;

namespace StrataLint.Scribe;

public static class StatementProjectionReconciliation
{
    private const string ReportRelativePath = ".lake/build/stratalint/raw-lean-report.json";

    public static void Verify(string repositoryRoot, bool requireLiveReport)
    {
        var reportPath = Path.Combine(repositoryRoot, ReportRelativePath);
        if (!File.Exists(reportPath))
        {
            if (requireLiveReport)
                throw new FileNotFoundException(
                    $"Required live raw Lean report is absent at '{reportPath}'.",
                    reportPath);
            return;
        }

        using var pilot = LoadFixture(repositoryRoot, "statement-projection-pilot-v1.json");
        using var expansion = LoadFixture(repositoryRoot, "statement-projection-expansion-v1.json");
        using var report = JsonDocument.Parse(File.ReadAllBytes(reportPath));
        var expected = new[] { pilot, expansion }
            .SelectMany(fixture => fixture.RootElement.GetProperty("declarations").EnumerateArray())
            .ToDictionary(
                item => item.GetProperty("name").GetString()!,
                item => item.GetProperty("type").GetString()!,
                StringComparer.Ordinal);
        var actual = report.RootElement.GetProperty("modules")
            .EnumerateArray()
            .SelectMany(module => module.GetProperty("declarations").EnumerateArray())
            .Where(item => expected.ContainsKey(item.GetProperty("name").GetString()!))
            .GroupBy(item => item.GetProperty("name").GetString()!, StringComparer.Ordinal)
            .ToDictionary(
                group => group.Key,
                group => group.Single().GetProperty("type").GetString()!,
                StringComparer.Ordinal);

        if (expected.Count != actual.Count
            || expected.Any(item => !actual.TryGetValue(item.Key, out var type)
                || !StringComparer.Ordinal.Equals(item.Value, type)))
        {
            throw new InvalidDataException(
                "Pinned statement-v1 projection fixtures do not match the live canonical raw Lean report.");
        }
    }

    private static JsonDocument LoadFixture(string repositoryRoot, string name) =>
        JsonDocument.Parse(File.ReadAllBytes(Path.Combine(repositoryRoot, "Golden", "Projection", name)));
}
