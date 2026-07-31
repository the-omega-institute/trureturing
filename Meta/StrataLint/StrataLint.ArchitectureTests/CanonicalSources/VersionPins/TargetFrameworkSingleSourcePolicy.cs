using System.Text.RegularExpressions;

namespace StrataLint.ArchitectureTests;

internal sealed record TargetFrameworkLiteralFinding(string Path, string Message);

internal static class TargetFrameworkSingleSourcePolicy
{
    private const string CanonicalOwner = "Directory.Build.props";
    private const string SyntheticLockFixture =
        "Meta/StrataLint/StrataLint.ArchitectureTests/Determinism/BannedApiConfigurationTests.cs";

    private static readonly Regex TargetFrameworkPattern = new(
        "(?<![A-Za-z0-9])net[0-9]+\\.[0-9]+(?![A-Za-z0-9.])",
        RegexOptions.CultureInvariant);

    internal static IReadOnlyList<TargetFrameworkLiteralFinding> InspectRepository(
        string repositoryRoot)
    {
        var findings = new List<TargetFrameworkLiteralFinding>();
        foreach (var file in GitIndexRepositoryFiles.Enumerate(repositoryRoot))
        {
            if (!IsInspectedExtension(Path.GetExtension(file.RelativePath)))
            {
                continue;
            }

            findings.AddRange(InspectText(
                file.RelativePath,
                File.ReadAllText(file.FullPath)));
        }

        return findings;
    }

    internal static IReadOnlyList<TargetFrameworkLiteralFinding> InspectText(
        string path,
        string source)
    {
        if (string.Equals(path, CanonicalOwner, StringComparison.Ordinal)
            || string.Equals(path, SyntheticLockFixture, StringComparison.Ordinal)
            || path.EndsWith("/packages.lock.json", StringComparison.Ordinal))
        {
            return [];
        }

        return TargetFrameworkPattern.Matches(source)
            .Select(match => new TargetFrameworkLiteralFinding(
                path,
                $"target framework literal {match.Value} is copied outside {CanonicalOwner}; resolve MSBuild TargetPath"))
            .ToArray();
    }

    private static bool IsInspectedExtension(string extension) => extension is
        ".cs" or ".csproj" or ".json" or ".props" or ".sh" or ".targets" or ".toml" or
        ".yaml" or ".yml";
}
