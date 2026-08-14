namespace StrataLint.Engine;

internal static class DigestionDecompositionPolicy
{
    internal static bool RejectsNewAbsorption(
        DigestionAtom atom,
        DigestionMigrationState candidate,
        int unresolvedSubitemCount,
        bool hasVerifiedChainAtoms,
        DigestionMigrationState? baseline) =>
        candidate == DigestionMigrationState.Absorbed
        && baseline != DigestionMigrationState.Absorbed
        && unresolvedSubitemCount == 0
        && !hasVerifiedChainAtoms
        && IsMultiClause(atom);

    internal static bool IsMultiClause(DigestionAtom atom)
    {
        ArgumentNullException.ThrowIfNull(atom);
        var lines = atom.RawBytes.AsSpan().IsEmpty
            ? Array.Empty<string>()
            : System.Text.Encoding.UTF8.GetString(atom.RawBytes.AsSpan())
                .Split('\n', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries);
        var explicitSections = lines
            .Skip(1)
            .Count(static line => line.StartsWith("**", StringComparison.Ordinal));
        var listClaims = lines.Count(static line =>
            line.StartsWith("- ", StringComparison.Ordinal)
            || line.StartsWith("* ", StringComparison.Ordinal));
        return explicitSections > 0 || listClaims > 1;
    }
}
