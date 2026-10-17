using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;

namespace StrataLint.Engine;

internal sealed partial class LeanSourceCatalog
{
    private readonly ImmutableDictionary<string, CompleteSourceFile> completeSources;
    private readonly ImmutableHashSet<string> completeSourceModules;
    private readonly ImmutableHashSet<string> unchangedSourceModules;

    private sealed record CompleteSourceFile(RepoPath Path, string Hash)
    {
        internal static CompleteSourceFile Create(RepositoryFile file) => new(file.Path,
            Convert.ToHexStringLower(SHA256.HashData(file.RawBytes.AsSpan())));
    }

    // Complete source equality retains every managed import, ambient command
    // and proof body, together with the complete recorded root inventory.
    private bool TryExtractCompleteSource(
        RepoPath path,
        ImmutableArray<FrozenDeclaration> recordedDeclarations,
        out ImmutableArray<byte> result,
        bool includeUnchangedClosure = false,
        bool forceComplete = false)
    {
        result = [];
        if (!forceComplete && completeSourceModules.IsEmpty
            && (!includeUnchangedClosure || unchangedSourceModules.IsEmpty)) return false;
        var visited = new HashSet<string>(StringComparer.Ordinal);
        var queue = new Queue<string>();
        queue.Enqueue(ModuleName(path));
        while (queue.TryDequeue(out var module))
        {
            if (!visited.Add(module)) continue;
            if (!completeSources.ContainsKey(module)
                || !importsByModule.TryGetValue(module, out var imports))
                throw new LeanSourceExtractionException($"Managed Lean source is missing for {module}.");
            foreach (var imported in imports)
            {
                if (LeanClosureValidator.IsManagedLean(imported.Replace('.', '/') + ".lean"))
                    queue.Enqueue(imported);
            }
        }
        if (!forceComplete && !visited.Overlaps(completeSourceModules)
            && (!includeUnchangedClosure || !visited.All(unchangedSourceModules.Contains)
                || !recordedDeclarations.All(declaration => PrivateModuleIsInClosure(declaration, visited))))
            return false;

        var output = new StringBuilder();
        AppendField(output, "source-mode", "complete-managed-import-closure");
        foreach (var declaration in recordedDeclarations.OrderBy(
            static declaration => declaration.DeclarationNameKey, StringComparer.Ordinal)
            .ThenBy(static declaration => declaration.Kind, StringComparer.Ordinal))
        {
            AppendField(output, "root-key", declaration.DeclarationNameKey);
            AppendField(output, "root-kind", declaration.Kind);
        }
        foreach (var source in visited.Select(module => completeSources[module])
            .OrderBy(static source => source.Path.Value, StringComparer.Ordinal))
        {
            AppendField(output, "source-path", source.Path.Value);
            AppendField(output, "source-sha256", source.Hash);
        }
        result = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(output.ToString()));
        return true;
    }
    internal ImmutableArray<byte> ExtractCompletePropositionSource(RepoPath path,
        ImmutableArray<FrozenDeclaration> declarations)
    {
        // Keep ordinary source, kind and private-origin validation before the full comparison.
        _ = ExtractPropositionSource(path, declarations);
        if (TryExtractCompleteSource(path, declarations, out var source, forceComplete: true)) return source;
        throw new LeanSourceExtractionException("Complete Lean source closure is unavailable.");
    }

    private static bool PrivateModuleIsInClosure(FrozenDeclaration declaration, HashSet<string> modules)
    {
        var components = CanonicalLeanNameDecoder.ComponentsPrefix(
            declaration.DeclarationNameKey, 0, out var consumed);
        if (components.Length == 0 || components[0].Value != "_private") return true;
        var index = Array.FindIndex(components, static part => part.Kind == "nn");
        if (consumed != declaration.DeclarationNameKey.Length || index < 2
            || index == components.Length - 1 || components[index].Value != "0"
            || components[..index].Any(static part => part.Kind != "ns")
            || components[(index + 1)..].Any(static part => part.Kind != "ns")) return false;
        var owner = components[1..index].Select(static part => part.Value);
        return modules.Any(module => owner.SequenceEqual(FullNameSegments(module)));
    }

}
