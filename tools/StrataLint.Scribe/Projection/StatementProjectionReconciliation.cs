using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public static class StatementProjectionReconciliation
{
    private const string FixtureRoot = "Golden/Projection/";

    internal static bool IsAffectedBy(RawChangeSet? changes)
    {
        if (changes is null)
        {
            return true;
        }

        return changes.Paths.Any(static path =>
            path.Value.StartsWith(FixtureRoot, StringComparison.Ordinal)
                && path.Value.EndsWith(".json", StringComparison.Ordinal)
            || IsImplementationInput(path.Value));
    }

    public static void Verify(string repositoryRoot, DeclarationCatalog catalog)
    {
        ArgumentNullException.ThrowIfNull(catalog);
        var findings = Check(repositoryRoot, catalog.Declarations);
        if (!findings.IsEmpty)
        {
            throw new InvalidDataException(
                "Pinned statement-v1 projection fixtures do not match the live canonical raw Lean report."
                + Environment.NewLine
                + string.Join(Environment.NewLine, findings));
        }
    }

    public static ImmutableArray<string> Check(string repositoryRoot, DeclarationCatalog catalog)
    {
        ArgumentNullException.ThrowIfNull(catalog);
        return Check(repositoryRoot, catalog.Declarations);
    }

    private static ImmutableArray<string> Check(
        string repositoryRoot,
        IEnumerable<LeanDeclaration> declarations)
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
                group => group.ToArray(),
                StringComparer.Ordinal);
        var findings = ImmutableArray.CreateBuilder<string>();

        foreach (var item in expected.OrderBy(static item => item.Key, StringComparer.Ordinal))
        {
            if (!actual.TryGetValue(item.Key, out var live))
            {
                findings.Add($"pinned statement projection is missing from live report: {item.Key}");
            }
            else if (live.Length != 1)
            {
                findings.Add(
                    $"pinned statement projection is ambiguous in live report: {item.Key} ({live.Length} declarations)");
            }
            else if (!StringComparer.Ordinal.Equals(item.Value, live[0].LoadTypeRepresentation()))
            {
                findings.Add($"pinned statement projection differs from live report: {item.Key}");
            }
        }

        return findings.ToImmutable();
    }

    private static JsonDocument LoadFixture(string repositoryRoot, string name) =>
        JsonDocument.Parse(File.ReadAllBytes(Path.Combine(repositoryRoot, "Golden", "Projection", name)));

    private static bool IsImplementationInput(string path)
    {
        if ((path.StartsWith("tools/StrataLint.Scribe/", StringComparison.Ordinal)
                || path.StartsWith("tools/StrataLint.Engine/", StringComparison.Ordinal))
            && (path.EndsWith(".cs", StringComparison.Ordinal)
                || path.EndsWith(".csproj", StringComparison.Ordinal)
                || path.EndsWith("/packages.lock.json", StringComparison.Ordinal)))
        {
            return true;
        }

        var fileName = path[(path.LastIndexOf('/') + 1)..];
        return fileName == "global.json"
            || fileName.StartsWith("Directory.Build.", StringComparison.Ordinal)
            || fileName.StartsWith("Directory.Packages.", StringComparison.Ordinal)
            || fileName.Equals("NuGet.Config", StringComparison.OrdinalIgnoreCase);
    }
}
