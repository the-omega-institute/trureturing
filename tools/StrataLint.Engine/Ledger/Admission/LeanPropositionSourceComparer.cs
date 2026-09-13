using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record LeanSourceComparisonFailure(RepoPath Path, int Line, string Message);
internal sealed record LeanSourceComparisonResult(ImmutableArray<LeanSourceComparisonFailure> Failures)
{
    internal bool Equivalent => Failures.IsEmpty;
}

internal static class LeanPropositionSourceComparer
{
    internal static bool AreEquivalent(RepositorySnapshot protectedBase, RepositorySnapshot candidate,
        ImmutableHashSet<RepoPath> reanchoredPaths, FrozenLedgerBaseView baseView,
        FrozenMaterialCatalog candidateCatalog, LeanSourceContextInput? input = null) =>
        Compare(protectedBase, candidate, reanchoredPaths, baseView, candidateCatalog, input).Equivalent;

    internal static LeanSourceComparisonResult Compare(RepositorySnapshot protectedBase,
        RepositorySnapshot candidate, ImmutableHashSet<RepoPath> reanchoredPaths,
        FrozenLedgerBaseView baseView, FrozenMaterialCatalog candidateCatalog,
        LeanSourceContextInput? input = null)
    {
        input ??= LeanSourceContextInput.Empty;
        var failures = ImmutableArray.CreateBuilder<LeanSourceComparisonFailure>();
        foreach (var path in reanchoredPaths.OrderBy(path => path.Value, StringComparer.Ordinal))
        {
            try
            {
                if (!baseView.ActiveByPath.TryGetValue(path, out var recorded)
                    || !candidateCatalog.ByPath.TryGetValue(path, out var current))
                    throw new LeanSourceExtractionException("Required frozen declaration material is missing.");
                if (!Pair(null))
                    throw new LeanSourceExtractionException("Required proposition or non-proof dependency source changed.");
                // Evaluate the finite lexical alternative before asking for historical
                // source. Equal pairs (including proof/whitespace edits) need no query.
                bool alternative;
                try { alternative = Pair(true); }
                catch (LeanSourceExtractionException exception) when (exception.IsLexical)
                {
                    // A delimiter Char does not admit an identifier interpretation.
                    continue;
                }
                if (!alternative && (!Pair(null, "protected") || !Pair(null, "current")))
                    throw new LeanSourceExtractionException(
                        "Source-supported equality-token interpretation exposes a changed required dependency.",
                        CollisionLine(candidate.Files[path].Text));

                bool Pair(bool? equality, string? sourceReference = null)
                {
                    var before = LeanSourceCatalog.Parse(protectedBase, input, "protected", equality, sourceReference)
                        .ExtractPropositionSource(path, recorded.Material.DeclarationStatementIds);
                    var after = LeanSourceCatalog.Parse(candidate, input, "current", equality, sourceReference)
                        .ExtractPropositionSource(path, current.DeclarationStatementIds);
                    return before.AsSpan().SequenceEqual(after.AsSpan());
                }
            }
            catch (LeanSourceExtractionException exception)
            {
                failures.Add(new(path, exception.Line ?? 1, exception.Message));
            }
        }
        return new(failures.ToImmutable());
    }

    private static int CollisionLine(string source)
    {
        var site = source.IndexOf("='", StringComparison.Ordinal);
        return site < 0 ? 1 : 1 + source.AsSpan(0, site).Count('\n');
    }
}

internal sealed class LeanSourceExtractionException(string message, int? line = null, bool lexical = false)
    : FormatException(message)
{
    internal int? Line { get; } = line;
    internal bool IsLexical { get; } = lexical;
}
