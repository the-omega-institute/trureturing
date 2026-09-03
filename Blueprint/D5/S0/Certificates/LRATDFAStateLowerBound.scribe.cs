using static StrataLint.Scribe;

namespace Blueprint.D5.S0.Certificates;

[Node("D5/S0/Certificates/LRATDFAStateLowerBound", Title = "LRAT-certified DFAO state lower bound", Role = NodeRole.Theorem, Status = NodeStatus.Proved, Owner = "agent", Summary = "Use a checked contradiction for a complete finite encoding to exclude the corresponding global bounded-state model.")]
public static class LRATDFAStateLowerBound
{
    [Claim("M06_refutation_complete_direction", Kind = ClaimKind.Theorem, Proven = true)]
    public static string RefutationDirection()
        => ForAll("P", "E", "R",
            Implies(
                And(
                    Math("P implies satisfiable(E.formula)"),
                    Math("R certifies E.formula inconsistent")),
                Math("P is empty")));

    [Claim("M06_finite_to_global", Kind = ClaimKind.Theorem, Proven = true)]
    public static string FiniteToGlobal()
        => ForAll("G", "F", "E", "R",
            Implies(
                And(
                    Math("G implies F"),
                    Math("E completely encodes F for refutation"),
                    Math("R certifies E.formula inconsistent")),
                Math("G is empty")));

    [Claim("M06_exact_minimality", Kind = ClaimKind.Theorem, Proven = true)]
    public static string ExactMinimality()
        => ForAll("P", "m", "N",
            Implies(
                And(
                    Math("P has an m-state global model"),
                    Math("the N-prefix excludes budgets through m-1")),
                Math("m is the minimal state count")));
}
