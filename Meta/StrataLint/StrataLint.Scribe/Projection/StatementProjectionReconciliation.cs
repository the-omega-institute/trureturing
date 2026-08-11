using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class StatementProjectionReconciliation
{
    public static void Verify(string repositoryRoot, DeclarationCatalog catalog)
    {
        ArgumentNullException.ThrowIfNull(catalog);
        Verify(repositoryRoot, catalog.Declarations);
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
