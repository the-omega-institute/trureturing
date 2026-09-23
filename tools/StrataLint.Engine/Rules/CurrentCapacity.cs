using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private static ImmutableArray<RuleFinding> CurrentCapacity(CurrentRuleContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        string[] materials;
        try { materials = RegisteredCheckMaterials.Read(context.Current, "SL-003"); }
        catch (InvalidDataException exception)
        {
            return [new RuleFinding(RegisteredCheckMaterials.ManifestPath, exception.Message)];
        }
        foreach (var material in materials.Where(static path => !IsArtifactLineCapacityExcluded(path)))
        {
            var path = RepoPath.CreateKnown(material);
            var count = CountArtifactLines(context.Current.Files[path].Text);
            if (count > ArtifactHardLineLimit)
                findings.Add(new(path.Value, $"artifact exceeds {ArtifactHardLineLimit} lines"));
            else if (count > ArtifactSoftLineLimit)
                findings.Add(new(path.Value, $"artifact spans {count} lines (soft limit {ArtifactSoftLineLimit}, hard limit {ArtifactHardLineLimit})", AdmissionEffect.Observe));
        }
        foreach (var (directory, paths) in CapacityPathsByDirectory(context.Current.Files.Keys))
            if (paths.Count > DirectoryToleranceLimit)
                findings.Add(new(directory, $"directory contains {paths.Count} files (repository tolerance {DirectoryToleranceLimit})"));
        return findings.ToImmutable();
    }
}
