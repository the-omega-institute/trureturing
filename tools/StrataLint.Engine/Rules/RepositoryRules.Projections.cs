using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private const string BlueprintPrefix = "Blueprint/";

    private static ImmutableArray<RuleFinding> BlueprintProjectionSource(
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
                "Blueprint Scribe source has no matching .md committed oracle")));

        var changedMarkdown = context.Changes.Paths
            .Where(static path => IsBlueprintPath(path.Value, ".md"))
            .Where(path => ContentDiffers(context.Current, context.Baseline, path.Value))
            .ToImmutableArray();
        if (changedMarkdown.IsDefaultOrEmpty)
        {
            return findings.ToImmutable();
        }

        var hasChangedScribeSource = context.Changes.Paths.Any(path =>
            IsBlueprintPath(path.Value, ".scribe.cs")
            && ContentDiffers(context.Current, context.Baseline, path.Value));
        var digestionEmissions = hasChangedScribeSource
            ? []
            : ChangedDigestionEmissionPaths(context);
        findings.AddRange(changedMarkdown
            .Where(path => !hasChangedScribeSource && !digestionEmissions.Contains(path.Value))
            .Select(static path => new RuleFinding(
                path.Value,
                "Blueprint markdown is a committed renderer oracle: update it from a Scribe or digestion source change")));
        return findings.ToImmutable();
    }

    private static bool IsProtectedCandidateOnlyScribeGrowth(
        RuleEvaluationContext context,
        string path) =>
        !context.Baseline.TryGetFile(path, out _)
        && context.Changes.Paths.Any(changed => changed.Value == path)
        && RepoPath.TryCreate(path, out var repoPath)
        && BootstrapGate.IsProtected(repoPath);

    private static HashSet<string> ChangedDigestionEmissionPaths(RuleEvaluationContext context)
    {
        var atomIds = context.Changes.Paths
            .Where(path => BackfillInventoryLoader.IsCanonicalPath(path.Value)
                && path.Value.EndsWith(".yaml", StringComparison.Ordinal)
                && ContentDiffers(context.Current, context.Baseline, path.Value))
            .Select(static path => path.Value[(path.Value.LastIndexOf('/') + 1)..^".yaml".Length])
            .ToHashSet(StringComparer.Ordinal);
        if (atomIds.Count == 0)
        {
            return [];
        }

        try
        {
            return BackfillInventoryLoader.Load(context.Current)
                .RequireDigestionEntries()
                .Where(entry => atomIds.Contains(entry.AtomId))
                .SelectMany(static entry => entry.CoverageGids)
                .Select(static gid => (Gid: gid, Separator: gid.LastIndexOf('.')))
                .Where(static item => item.Separator > item.Gid.LastIndexOf('/'))
                .Select(static item => item.Gid[..item.Separator])
                .Select(ScribeEmissionAttestation.EmissionPath)
                .ToHashSet(StringComparer.Ordinal);
        }
        catch (FormatException)
        {
            return [];
        }
    }

    private static bool IsBlueprintPath(string path, string suffix) =>
        path.StartsWith(BlueprintPrefix, StringComparison.Ordinal)
        && path.EndsWith(suffix, StringComparison.Ordinal);

    private static bool ContentDiffers(
        RepositorySnapshot current,
        RepositorySnapshot baseline,
        string path)
    {
        var hasCurrent = current.TryGetFile(path, out var currentFile);
        var hasBaseline = baseline.TryGetFile(path, out var baselineFile);
        return hasCurrent != hasBaseline
            || hasCurrent && !currentFile!.RawBytes.SequenceEqual(baselineFile!.RawBytes);
    }
}
