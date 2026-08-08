using System.Text.Json;
using StrataLint.Engine;

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

        using var report = JsonDocument.Parse(File.ReadAllBytes(reportPath));
        Verify(repositoryRoot, report.RootElement.GetProperty("modules")
            .EnumerateArray()
            .SelectMany(module => module.GetProperty("declarations").EnumerateArray())
            .Select(item => new LeanDeclaration(
                item.GetProperty("name").GetString()!,
                item.TryGetProperty("kind", out var kind) ? kind.GetString()! : "theorem",
                item.GetProperty("type").GetString()!,
                [])));
    }

    public static void Verify(string repositoryRoot, LeanAxiomReport report)
    {
        ArgumentNullException.ThrowIfNull(report);
        Verify(repositoryRoot, report.Files.Values.SelectMany(static file => file.Declarations));
    }

    private static void Verify(string repositoryRoot, IEnumerable<LeanDeclaration> declarations)
    {
        using var pilot = LoadFixture(repositoryRoot, "statement-projection-pilot-v1.json");
        using var expansion = LoadFixture(repositoryRoot, "statement-projection-expansion-v1.json");
        var expected = new[] { pilot, expansion }
            .SelectMany(fixture => fixture.RootElement.GetProperty("declarations").EnumerateArray())
            .ToDictionary(
                item => item.GetProperty("name").GetString()!,
                item => item.GetProperty("type").GetString()!,
                StringComparer.Ordinal);
        var actual = declarations
            .Where(item => expected.ContainsKey(item.Name))
            .GroupBy(item => item.Name, StringComparer.Ordinal)
            .ToDictionary(
                group => group.Key,
                group => group.Single().TypeRepresentation,
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
