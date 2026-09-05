using System.Collections.Immutable;
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
        var findings = Check(repositoryRoot, catalog);
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
        var expected = StatementProjectionFixtureLoader.LoadStatements(repositoryRoot).Values
            .SelectMany(static module => module);
        var findings = ImmutableArray.CreateBuilder<string>();

        foreach (var item in expected.OrderBy(static item => item.SourcePath.Value, StringComparer.Ordinal)
                     .ThenBy(static item => item.Name, StringComparer.Ordinal))
        {
            var live = catalog.DeclarationsFor(item.SourcePath, item.Name);
            var identity = $"{item.Name} ({item.SourcePath.Value})";
            if (live.IsEmpty)
            {
                findings.Add($"pinned statement projection is missing from live report: {identity}");
            }
            else if (live.Length != 1)
            {
                findings.Add(
                    $"pinned statement projection is ambiguous in live report: {identity} ({live.Length} declarations)");
            }
            else if (!StringComparer.Ordinal.Equals(item.Kind, live[0].Kind)
                     || !StringComparer.Ordinal.Equals(item.Type, live[0].LoadTypeRepresentation()))
            {
                findings.Add($"pinned statement projection differs from live report: {identity}");
            }
        }

        return findings.ToImmutable();
    }

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
