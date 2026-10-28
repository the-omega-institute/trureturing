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
        return DigestionDecomposition.PlanClauses(atom) is not null;
    }
}
