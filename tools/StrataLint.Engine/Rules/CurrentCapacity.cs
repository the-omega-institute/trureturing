using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private static ImmutableArray<RuleFinding> CurrentCapacity(CurrentRuleContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        foreach (var (path, file) in context.Current.Files.Where(static pair => !IsCapacityExcluded(pair.Key.Value)))
        {
            var count = CountArtifactLines(file.Text);
            if (count > ArtifactHardLineLimit)
                findings.Add(new(path.Value, "artifact exceeds 800 lines"));
            else if (count > ArtifactSoftLineLimit)
                findings.Add(new(path.Value, $"artifact spans {count} lines (soft limit {ArtifactSoftLineLimit}, hard limit {ArtifactHardLineLimit})", AdmissionEffect.Observe));
        }
        foreach (var (directory, paths) in CapacityPathsByDirectory(context.Current.Files.Keys))
            if (paths.Count > DirectoryToleranceLimit)
                findings.Add(new(directory, $"directory contains {paths.Count} files (repository tolerance {DirectoryToleranceLimit})"));
        return findings.ToImmutable();
    }
}
