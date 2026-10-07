namespace StrataLint.Engine;

internal static class DigestionDecompositionPolicy
{
    internal static bool RejectsUndecomposedAbsorption(
        DigestionAtom atom,
        DigestionMigrationState candidate,
        int unresolvedSubitemCount,
        bool hasVerifiedChainAtoms) =>
        candidate == DigestionMigrationState.Absorbed
        && unresolvedSubitemCount == 0
        && !hasVerifiedChainAtoms
        && IsMultiClause(atom);

    internal static bool IsMultiClause(DigestionAtom atom)
    {
        ArgumentNullException.ThrowIfNull(atom);
        var lines = DigestionDecomposition.Lines(System.Text.Encoding.UTF8.GetString(atom.RawBytes.AsSpan()))
            .Select(static line => line.Text).ToArray();
        var explicitSections = lines
            .Skip(1)
            .Count(static line => line.StartsWith("**", StringComparison.Ordinal));
        var listClaims = lines.Count(static line =>
            line.StartsWith("- ", StringComparison.Ordinal)
            || line.StartsWith("* ", StringComparison.Ordinal));
        return explicitSections > 0 || listClaims > 1;
    }
}
