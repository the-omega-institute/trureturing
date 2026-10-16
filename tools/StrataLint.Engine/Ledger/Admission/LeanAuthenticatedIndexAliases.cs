using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class LeanAuthenticatedIndexAliases
{
    internal static bool AreEquivalent(RepoPath path, FrozenStateRecord recorded, LeanFileReport current,
        LeanSourceCatalog baseSources, LeanSourceCatalog candidateSources, FrozenStatementWitness witness)
    {
        if (!witness.TryAuthenticate(path, recorded, out var oldStatements)
            || current.Declarations.Select(static row => row.NameKey).Distinct(StringComparer.Ordinal).Count()
                != current.Declarations.Length) return false;
        var candidateRoots = FrozenStateRecord.Project(current);
        var candidateSet = candidateRoots.ToImmutableHashSet();
        var removed = recorded.Declarations.Where(root => !candidateSet.Contains(root)).ToImmutableArray();
        if (removed.IsEmpty) return false;
        foreach (var alias in removed)
        {
            if (alias.Kind != "def" || !TryAliasOwner(alias.DeclarationNameKey, out var ownerKey)
                || current.Declarations.Any(row => row.NameKey == alias.DeclarationNameKey)) return false;
            var canonicalKey = $"ns({ownerKey},7:ctorIdx)";
            foreach (var root in new[] { new FrozenDeclaration(ownerKey, "inductive"), new FrozenDeclaration(canonicalKey, "def") })
                if (!recorded.Declarations.Contains(root) || !candidateSet.Contains(root)) return false;
            if (!baseSources.HasExactIndexAliasOwner(path, ownerKey, alias.DeclarationNameKey, canonicalKey)
                || !candidateSources.HasExactIndexAliasOwner(path, ownerKey, alias.DeclarationNameKey, canonicalKey)) return false;
            var material = $"statement-v1(uparams=[],type=ep(bd,ec({ownerKey},[]),ec(ns(n0,3:Nat),[])),value=ec({canonicalKey},[]))";
            // A new declaration object cannot return the witness's precomputed identity.
            var expected = CanonicalStatementWriter.DeclarationStatementId(path,
                new LeanDeclaration(alias.DeclarationNameKey, "def", material, []) { NameKey = alias.DeclarationNameKey });
            if (!oldStatements.Any(row => row.DeclarationNameKey == alias.DeclarationNameKey
                && row.Kind == "def" && row.StatementId.Value == expected)) return false;
        }
        var removedSet = removed.ToImmutableHashSet();
        var retained = recorded.Declarations.Where(root => !removedSet.Contains(root)).ToImmutableArray();
        return retained.SequenceEqual(candidateRoots)
            && baseSources.ExtractCompletePropositionSource(path, retained).AsSpan()
                .SequenceEqual(candidateSources.ExtractCompletePropositionSource(path, candidateRoots).AsSpan());
    }

    private static bool TryAliasOwner(string key, out string owner)
    {
        owner = string.Empty;
        try
        {
            var parts = CanonicalLeanNameDecoder.ComponentsPrefix(key, 0, out var consumed);
            const string suffix = ",9:toCtorIdx)";
            if (consumed != key.Length || parts.Length < 2 || parts[^1].Kind != "ns"
                || parts[^1].Value != "toCtorIdx" || !key.EndsWith(suffix, StringComparison.Ordinal)) return false;
            owner = key.Substring(3, key.Length - 3 - suffix.Length);
            return true;
        }
        catch (FormatException) { return false; }
    }
}

internal sealed partial class LeanSourceCatalog
{
    internal bool HasExactIndexAliasOwner(RepoPath path, string ownerKey, string aliasKey, string canonicalKey)
    {
        var moduleDeclarations = declarations.Where(declaration => declaration.Path == path).ToImmutableArray();
        if (moduleDeclarations.IsEmpty) return false;
        (string Kind, string Value)[] components;
        try
        {
            components = CanonicalLeanNameDecoder.ComponentsPrefix(ownerKey, 0, out var consumed);
            if (consumed != ownerKey.Length || components.Length == 0) return false;
        }
        catch (FormatException) { return false; }
        var privateOwner = components[0] == ("ns", "_private");
        if (!privateOwner && components.Any(static part => part.Kind != "ns")) return false;
        var ownerSegments = components.Select(static part => part.Value).ToImmutableArray();
        var matches = ResolveExactRecordedSources(moduleDeclarations[0], ownerSegments, ownerKey).ToImmutableArray();
        return matches.Length == 1 && matches[0].Path == path && matches[0].Kind == "inductive"
            && matches[0].IsPrivate == privateOwner
            && !ResolveExactRecordedSources(moduleDeclarations[0], ownerSegments.Add("toCtorIdx"), aliasKey).Any()
            && !ResolveExactRecordedSources(moduleDeclarations[0], ownerSegments.Add("ctorIdx"), canonicalKey).Any();
    }
}
