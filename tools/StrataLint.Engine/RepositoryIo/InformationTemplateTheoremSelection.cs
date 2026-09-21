using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class InformationTemplateTheoremSelection
{
    internal static ImmutableHashSet<RepoPath> OwnerMirrors(RepositorySnapshot snapshot, LeanAxiomReport report,
        RepoPath source, ImmutableHashSet<string> theorems)
    {
        var mirror = RepoPath.CreateKnown("Reg/" + source.Value);
        if (!snapshot.Files.ContainsKey(mirror)) return [];
        // The source path is authoritative, including when the theorem's namespace
        // differs from its module. Only imports of this exact mirror reach variants.
        return LeanImportClosure.RepositoryPaths(report, mirror)
            .Where(path => InformationTemplateSelection.IsRegSource(path) && snapshot.Files.ContainsKey(path)
                && (path == mirror || report.Files.TryGetValue(path, out var module)
                    && module.InformationTemplates is { } payload
                    && InformationTemplateSelection.HasTheorems(payload, theorems)))
            .ToImmutableHashSet();
    }

    internal static InformationTemplateUniverse Collect(RepositorySnapshot snapshot, LeanAxiomReport report,
        RepoPath source, RepoPath owner, ImmutableHashSet<string> theorems, IEnumerable<RepoPath> mirrors)
    {
        var universe = InformationTemplateEvidence.Collect(snapshot, report, [owner], theorems, mirrors);
        var imports = LeanImportClosure.RepositoryPaths(report, owner);
        foreach (var occurrence in universe.Occurrences.Values)
            if (!imports.Contains(source) || imports.Sum(path => report.Files.TryGetValue(path, out var module)
                ? module.Declarations.Count(declaration => declaration.Name == occurrence.Key.Theorem
                    && declaration.Kind == "theorem") : 0) != 1)
                throw new FormatException("DTR-Evidence: registration does not import the unique theorem source owner");
        return universe;
    }
}
