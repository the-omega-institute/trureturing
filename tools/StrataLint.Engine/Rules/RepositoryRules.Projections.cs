using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private const string BlueprintPrefix = "Blueprint/";

    // This compares path stems only. It protects the source/projection skeleton,
    // never Markdown bytes, provenance, freshness, or history.
    private static ImmutableArray<RuleFinding> BlueprintProjectionSkeleton(
        RuleEvaluationContext context)
    {
        var markdown = context.Current.Files.Keys
            .Where(static path => IsBlueprintPath(path.Value, ".md"))
            .Select(static path => path.Value[..^".md".Length])
            .ToHashSet(StringComparer.Ordinal);
        var scribeSources = context.Current.Files.Keys
            .Where(static path => IsBlueprintPath(path.Value, ".scribe.cs"))
            .Select(static path => path.Value[..^".scribe.cs".Length])
            .ToHashSet(StringComparer.Ordinal);
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        findings.AddRange(markdown
            .Except(scribeSources, StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .Select(static stem => new RuleFinding(
                stem + ".md",
                "Blueprint markdown has no matching .scribe.cs source")));
        findings.AddRange(scribeSources
            .Except(markdown, StringComparer.Ordinal)
            .Where(stem => !IsProtectedCandidateOnlyScribeGrowth(
                context,
                stem + ".scribe.cs"))
            .Order(StringComparer.Ordinal)
            .Select(static stem => new RuleFinding(
                stem + ".scribe.cs",
                "Blueprint Scribe source has no matching .md projection")));
        return findings.ToImmutable();
    }

    private static bool IsProtectedCandidateOnlyScribeGrowth(
        RuleEvaluationContext context,
        string path) =>
        !context.Baseline.TryGetFile(path, out _)
        && context.Changes.Paths.Any(changed => changed.Value == path)
        && RepoPath.TryCreate(path, out var repoPath)
        && BootstrapGate.IsProtected(repoPath);

    private static bool IsBlueprintPath(string path, string suffix) =>
        path.StartsWith(BlueprintPrefix, StringComparison.Ordinal)
        && path.EndsWith(suffix, StringComparison.Ordinal);
}
