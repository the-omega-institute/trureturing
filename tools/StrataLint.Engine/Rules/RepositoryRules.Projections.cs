using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private const string BlueprintPrefix = "Blueprint/";

    // This compares path stems only. It protects the source/projection skeleton,
    // never Markdown bytes, provenance, freshness, or history.
    private static ImmutableArray<RuleFinding> BlueprintProjectionSkeleton(
        CurrentRuleContext context)
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
            .Where(stem => !BootstrapGate.IsProtected(RepoPath.CreateKnown(stem + ".scribe.cs")))
            .Order(StringComparer.Ordinal)
            .Select(static stem => new RuleFinding(
                stem + ".scribe.cs",
                "Blueprint Scribe source has no matching .md projection")));
        return findings.ToImmutable();
    }

    private static ImmutableArray<RuleFinding> ProtectedBlueprintSkeleton(DeltaRuleContext context) =>
        context.Current.Files.Keys
            .Where(path => IsBlueprintPath(path.Value, ".scribe.cs") && BootstrapGate.IsProtected(path))
            .Where(path => BlueprintStemAffected(context, path.Value[..^".scribe.cs".Length]))
            .Where(path => !context.Current.TryGetFile(path.Value[..^".scribe.cs".Length] + ".md", out _))
            .Where(path => !IsProtectedCandidateOnlyScribeGrowth(context, path.Value))
            .Select(static path => new RuleFinding(path.Value, "Blueprint Scribe source has no matching .md projection"))
            .ToImmutableArray();

    private static bool BlueprintStemAffected(DeltaRuleContext context, string stem) =>
        context.IsBaseFactAffected(stem + ".md")
        || context.IsBaseFactAffected(stem + ".scribe.cs");

    private static bool IsProtectedCandidateOnlyScribeGrowth(
        DeltaRuleContext context,
        string path) =>
        !context.Baseline.TryGetFile(path, out _)
        && context.Changes.Paths.Any(changed => changed.Value == path)
        && RepoPath.TryCreate(path, out var repoPath)
        && BootstrapGate.IsProtected(repoPath);

    private static bool IsBlueprintPath(string path, string suffix) =>
        path.StartsWith(BlueprintPrefix, StringComparison.Ordinal)
        && path.EndsWith(suffix, StringComparison.Ordinal);
}
