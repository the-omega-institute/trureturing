using System.Text.Json;
using System.Text.RegularExpressions;

namespace StrataLint.ArchitectureTests;

internal sealed record TheoryIsolationFinding(string Path, string Message);

internal static class TheoryIsolationPolicy
{
    private static readonly string FirstRetiredToken = string.Concat("gi", "ct");
    private static readonly string SecondRetiredToken = string.Concat("pz", "g");
    private static readonly Regex InternalTheoryReferencePattern = new(
        $"(?:{FirstRetiredToken}|{SecondRetiredToken})",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
    private static readonly Regex TheoryPathPattern = new(
        "docs/develop/" + "theory(?:/|\\\\)",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
    private static readonly HashSet<string> RetiredCatalogSchemes = new(
        [FirstRetiredToken, SecondRetiredToken],
        StringComparer.OrdinalIgnoreCase);

    private static readonly string[] AllowedCSharpPrefixes =
    [
        "Meta/StrataLint/StrataLint.Engine/Digestion/",
        "Meta/StrataLint/StrataLint.Engine/Rules/Backfill/",
    ];

    private const string DigestionTestsPrefix =
        "Meta/StrataLint/StrataLint.Tests/Digestion/";

    private static readonly HashSet<string> AllowedCSharpFiles = new(
        [
            DigestionTestsPrefix + "DigestionLedgerTests.cs",
            DigestionTestsPrefix + "TheoryAtomizerTests.cs",
        ],
        StringComparer.Ordinal);

    internal static readonly string AnchorCatalogPath = string.Concat(
        "Meta/StrataLint/Generated/",
        "anchor-catalog.v1.json");

    internal static IReadOnlyList<TheoryIsolationFinding> InspectRepository(string repositoryRoot)
    {
        var findings = CSharpRepositorySources.Enumerate(repositoryRoot)
            .SelectMany(source => InspectSource(
                source.RelativePath,
                File.ReadAllText(source.FullPath)))
            .ToList();

        foreach (var path in Directory.EnumerateFiles(repositoryRoot, "*.lean", SearchOption.AllDirectories))
        {
            var relativePath = Path.GetRelativePath(repositoryRoot, path).Replace('\\', '/');
            if (relativePath.Split('/').Any(static segment => segment is ".git" or ".lake" or "bin" or "obj"))
            {
                continue;
            }

            findings.AddRange(InspectSource(relativePath, File.ReadAllText(path)));
        }

        var fullCatalogPath = Path.Combine(repositoryRoot, AnchorCatalogPath);
        if (File.Exists(fullCatalogPath))
        {
            findings.AddRange(InspectCatalog(
                AnchorCatalogPath,
                File.ReadAllText(fullCatalogPath)));
        }

        return findings;
    }

    internal static IReadOnlyList<TheoryIsolationFinding> InspectSource(string path, string source)
    {
        if (path.EndsWith(".cs", StringComparison.Ordinal) && IsAllowedCSharp(path))
        {
            return [];
        }

        var findings = new List<TheoryIsolationFinding>();
        if (TheoryPathPattern.IsMatch(source))
        {
            findings.Add(new TheoryIsolationFinding(
                path,
                "program or formal source contains an internal theory reference path"));
        }

        if (InternalTheoryReferencePattern.IsMatch(source))
        {
            findings.Add(new TheoryIsolationFinding(
                path,
                "program or formal source contains an internal theory reference"));
        }

        return findings;
    }

    internal static IReadOnlyList<TheoryIsolationFinding> InspectCatalog(string path, string source)
    {
        try
        {
            using var document = JsonDocument.Parse(source);
            if (!document.RootElement.TryGetProperty("definitions", out var definitions)
                || definitions.ValueKind != JsonValueKind.Array)
            {
                return [];
            }

            return definitions.EnumerateArray()
                .Where(static definition => definition.TryGetProperty("anchor", out _))
                .Select(static definition => definition.GetProperty("anchor"))
                .Where(static anchor => anchor.ValueKind == JsonValueKind.String)
                .Select(static anchor => anchor.GetString())
                .Where(static anchor => anchor is not null)
                .Where(anchor => RetiredCatalogSchemes.Contains(anchor!.Split('/')[0]))
                .Select(_ => new TheoryIsolationFinding(
                    path,
                    "anchor catalog contains an internal theory scheme"))
                .ToArray();
        }
        catch (JsonException)
        {
            return [];
        }
    }

    private static bool IsAllowedCSharp(string path) =>
        AllowedCSharpFiles.Contains(path)
        || AllowedCSharpPrefixes.Any(prefix => path.StartsWith(prefix, StringComparison.Ordinal));
}
