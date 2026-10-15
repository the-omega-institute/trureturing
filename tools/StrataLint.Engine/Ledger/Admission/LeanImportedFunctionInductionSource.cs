using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal sealed partial class LeanSourceCatalog
{
    private readonly ImmutableDictionary<string, RepositoryFile> sourceModules;

    private LeanSourceDeclaration ResolveImportedFunctionInduction(
        LeanSourceDeclaration owner, FrozenDeclaration recorded, ImmutableArray<string> segments)
    {
        var parentName = string.Join('.', segments[..^1]);
        var fullName = string.Join('.', segments);
        if (recorded.Kind != "theorem" || IsPrivateNameKey(recorded.DeclarationNameKey)
            || DecodeNameKeySegments(recorded.DeclarationNameKey).Any(static segment => segment.IsNumeric)
            || !byFullName.TryGetValue(parentName, out var parentCandidates))
            throw Unresolved();

        var parents = parentCandidates.Where(source => source.Path != owner.Path && IsImported(owner, source))
            .ToImmutableArray();
        if (parents.Length != 1 || parents[0].Kind != "def" || parents[0].IsPrivateDeclaration
            || !parents[0].IsTopLevelDeclaration
            || parents[0].HasUnsafeOrMetaModifier
            || !FullNameSegments(parents[0].FullName).SequenceEqual(segments[..^1])
            || byFullName.TryGetValue(fullName, out var collisions)
                && collisions.Any(source => IsImported(owner, source)))
            throw Unresolved();

        // A reserved name does not establish compiler provenance. Bind every reachable
        // managed module's original bytes, including proof programs and source positions.
        var sources = ImmutableArray.CreateBuilder<RepositoryFile>();
        var queue = new Queue<string>([ModuleName(owner.Path)]);
        var visited = new HashSet<string>(StringComparer.Ordinal);
        while (queue.TryDequeue(out var module))
        {
            if (!visited.Add(module) || !sourceModules.TryGetValue(module, out var source)) continue;
            sources.Add(source);
            if (importsByModule.TryGetValue(module, out var imports))
                foreach (var import in imports) queue.Enqueue(import);
        }

        return owner with
        {
            FullName = fullName,
            Kind = "theorem",
            IsProof = false,
            SemanticTokens = [],
            AmbientTokens = [],
            ImportedInductionSources = sources.OrderBy(static source => source.Path.Value, StringComparer.Ordinal)
                .ToImmutableArray(),
        };

        LeanSourceExtractionException Unresolved() => new(
            $"Imported Lean function induction source cannot be resolved: {recorded.DeclarationNameKey}.");
    }

    private static void AppendImportedInductionSource(StringBuilder output, LeanSourceDeclaration root)
    {
        AppendField(output, "root-kind", "imported-function-induction-source-closure");
        AppendField(output, "root-name", root.FullName);
        foreach (var source in root.ImportedInductionSources)
        {
            AppendField(output, "source-path", source.Path.Value);
            AppendField(output, "source-bytes", Convert.ToBase64String(source.RawBytes.AsSpan()));
        }
    }
}
