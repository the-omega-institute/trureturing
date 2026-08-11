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
    private static readonly Regex LeanTaskPattern = new(
        "/-- TASK D5-T[0-9]{4} \\| 难度:[1-5] \\| 依赖:[^\\n|]+ \\| 尝试:[0-9]+\\n"
        + "\\s+提示:[^\\n]+\\n\\s+尸检:(?<autopsy>[^\\n]+) -/",
        RegexOptions.CultureInvariant);
    private static readonly string[] AllowedCSharpPrefixes =
    [
        "Meta/StrataLint/StrataLint.Engine/Digestion/",
        "Meta/StrataLint/StrataLint.Engine/Rules/Backfill/",
    ];

    private const string DigestionTestsPrefix =
        "Meta/StrataLint/StrataLint.Tests/Digestion/";

    private static readonly HashSet<string> AllowedCSharpFiles = new(
        [
            DigestionTestsPrefix + "DigestionAlignmentTests.cs",
            DigestionTestsPrefix + "DigestionAlignmentIntegrityTests.cs",
            DigestionTestsPrefix + "DigestionLedgerTests.cs",
            DigestionTestsPrefix + "FormalizeCandidatesTests.cs",
            DigestionTestsPrefix + "Atomizers/TheoryAtomizerTests.Cone.cs",
            DigestionTestsPrefix + "Atomizers/TheoryAtomizerTests.NumberedClaims.cs",
            DigestionTestsPrefix + "TheoryAtomizerTests.cs",
        ],
        StringComparer.Ordinal);

    internal static IReadOnlyList<TheoryIsolationFinding> InspectRepository(string repositoryRoot)
    {
        var repositoryFiles = GitIndexRepositoryFiles.Enumerate(repositoryRoot);
        var theoryBasenamePattern = CreateTheoryBasenamePattern(repositoryRoot);
        var findings = repositoryFiles
            .Where(static file => file.RelativePath.EndsWith(".cs", StringComparison.Ordinal))
            .SelectMany(source => InspectSource(
                source.RelativePath,
                File.ReadAllText(source.FullPath),
                theoryBasenamePattern))
            .ToList();

        foreach (var source in repositoryFiles.Where(static file =>
                     file.RelativePath.EndsWith(".lean", StringComparison.Ordinal)))
        {
            findings.AddRange(InspectSource(
                source.RelativePath,
                File.ReadAllText(source.FullPath),
                theoryBasenamePattern));
        }

        return findings;
    }

    internal static IReadOnlyList<TheoryIsolationFinding> InspectSource(string path, string source)
        => InspectSource(path, source, theoryBasenamePattern: null);

    internal static IReadOnlyList<TheoryIsolationFinding> InspectSource(
        string path,
        string source,
        string repositoryRoot) =>
        InspectSource(path, source, CreateTheoryBasenamePattern(repositoryRoot));

    private static IReadOnlyList<TheoryIsolationFinding> InspectSource(
        string path,
        string source,
        Regex? theoryBasenamePattern)
    {
        if (path.EndsWith(".cs", StringComparison.Ordinal) && IsAllowedCSharp(path))
        {
            return [];
        }

        var inspectedSource = path.EndsWith(".lean", StringComparison.Ordinal)
            ? MaskTaskAutopsies(source)
            : source;
        var findings = new List<TheoryIsolationFinding>();
        if (TheoryPathPattern.IsMatch(inspectedSource))
        {
            findings.Add(new TheoryIsolationFinding(
                path,
                "program or formal source contains an internal theory reference path"));
        }

        if (InternalTheoryReferencePattern.IsMatch(inspectedSource))
        {
            findings.Add(new TheoryIsolationFinding(
                path,
                "program or formal source contains an internal theory reference"));
        }

        if (theoryBasenamePattern?.IsMatch(inspectedSource) == true)
        {
            findings.Add(new TheoryIsolationFinding(
                path,
                "program or formal source contains an internal theory basename"));
        }

        return findings;
    }

    private static bool IsAllowedCSharp(string path) =>
        AllowedCSharpFiles.Contains(path)
        || AllowedCSharpPrefixes.Any(prefix => path.StartsWith(prefix, StringComparison.Ordinal));

    private static Regex? CreateTheoryBasenamePattern(string repositoryRoot)
    {
        var theoryRoot = Path.Combine(repositoryRoot, "docs", "develop", "theory");
        var basenames = Directory.EnumerateFiles(theoryRoot, "*", SearchOption.AllDirectories)
            .Where(static path =>
                (File.GetAttributes(path) & (FileAttributes.Directory | FileAttributes.ReparsePoint)) == 0)
            .Select(static path => new FileInfo(path).Name)
            .Distinct(StringComparer.Ordinal)
            .OrderByDescending(static basename => basename.Length)
            .ThenBy(static basename => basename, StringComparer.Ordinal)
            .Select(Regex.Escape)
            .ToArray();
        if (basenames.Length == 0)
        {
            return null;
        }

        return new Regex(
            $"(?<![A-Za-z0-9_-])(?:{string.Join('|', basenames)})(?![A-Za-z0-9_-])",
            RegexOptions.CultureInvariant);
    }

    private static string MaskTaskAutopsies(string source) =>
        LeanTaskPattern.Replace(source, static match =>
        {
            var autopsy = match.Groups["autopsy"];
            var relativeIndex = autopsy.Index - match.Index;
            return match.Value[..relativeIndex]
                + new string(' ', autopsy.Length)
                + match.Value[(relativeIndex + autopsy.Length)..];
        });
}
