using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;

namespace StrataLint.Engine;

internal sealed partial class LeanSourceCatalog
{
    private readonly ImmutableDictionary<string, CompleteSourceFile> completeSources;
    private readonly ImmutableHashSet<string> completeSourceModules;

    private sealed record CompleteSourceFile(RepoPath Path, string Hash)
    {
        internal static CompleteSourceFile Create(RepositoryFile file) => new(file.Path,
            Convert.ToHexStringLower(SHA256.HashData(file.RawBytes.AsSpan())));
    }

    // An unchanged unsupported file requires every managed import, including
    // ambient commands and proof bodies. Ordinary consumers use the same route.
    private bool TryExtractCompleteSource(
        RepoPath path,
        ImmutableArray<FrozenDeclaration> recordedDeclarations,
        out ImmutableArray<byte> result)
    {
        result = [];
        if (completeSourceModules.IsEmpty) return false;
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
        if (!visited.Overlaps(completeSourceModules)) return false;

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
}
