using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed partial class LeanSourceCatalog
{
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
        return owner with
        {
            FullName = fullName,
            Kind = "theorem",
            IsProof = false,
            SemanticTokens = [],
            AmbientTokens = [],
            ManagedSourceClosure = ReachableManagedSources(owner),
        };

        LeanSourceExtractionException Unresolved() => new(
            $"Imported Lean function induction source cannot be resolved: {recorded.DeclarationNameKey}.");
    }

}
