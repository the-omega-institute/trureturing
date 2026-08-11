using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private static ImmutableArray<RuleFinding> ScribeLegacyConstructorBudget(RuleEvaluationContext context)
    {
        var paths = context.Changes.Paths
            .Where(static path => IsBlueprintPath(path.Value, ".scribe.cs"))
            .ToImmutableArray();
        var deleted = paths
            .Where(path => context.Baseline.Files.ContainsKey(path) && !context.Current.Files.ContainsKey(path))
            .ToImmutableArray();
        var added = paths
            .Where(path => context.Current.Files.ContainsKey(path) && !context.Baseline.Files.ContainsKey(path))
            .ToImmutableArray();
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();

        var renameSources = new Dictionary<RepoPath, RepositoryFile>();
        foreach (var target in added)
        {
            var matches = deleted
                .Where(source => context.Baseline.Files[source].RawBytes
                    .SequenceEqual(context.Current.Files[target].RawBytes))
                .ToImmutableArray();
            if (matches.Length > 1
                || matches.Length == 1 && added.Count(other =>
                    context.Current.Files[other].RawBytes.SequenceEqual(
                        context.Baseline.Files[matches[0]].RawBytes)) > 1)
            {
                findings.Add(new RuleFinding(target.Value, "无法证明为纯搬移: 字节完全相同的 rename 配对不唯一"));
            }
            else if (matches.Length == 1)
            {
                renameSources[target] = context.Baseline.Files[matches[0]];
            }
        }

        foreach (var path in paths.Where(path => context.Current.Files.ContainsKey(path)))
        {
            var current = ScribeLegacyConstructorScanner.Count(context.Current.Files[path].Text);
            ImmutableDictionary<ScribeLegacyConstructor, int> baseline;
            if (context.Baseline.Files.TryGetValue(path, out var baselineFile))
            {
                baseline = ScribeLegacyConstructorScanner.Count(baselineFile.Text);
            }
            else if (renameSources.TryGetValue(path, out var renameSource))
            {
                baseline = ScribeLegacyConstructorScanner.Count(renameSource.Text);
            }
            else
            {
                baseline = Enum.GetValues<ScribeLegacyConstructor>()
                    .ToImmutableDictionary(static kind => kind, static _ => 0);
            }

            foreach (var kind in Enum.GetValues<ScribeLegacyConstructor>())
            {
                if (current[kind] > baseline[kind])
                {
                    findings.Add(new RuleFinding(
                        path.Value,
                        $"legacy Scribe constructor {kind} increased from {baseline[kind]} to {current[kind]}; remaining={current[kind]}"));
                }
            }
        }
        return findings.ToImmutable();
    }
}
