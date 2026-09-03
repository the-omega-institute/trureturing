using static StrataLint.Scribe;

namespace Blueprint.D5.S0.Certificates;

[Node("D5/S0/Certificates/ZeroAnchoredLRATDFAStateLowerBound", Title = "Zero-anchored LRAT state lower bound", Role = NodeRole.Theorem, Status = NodeStatus.Proved, Owner = "agent", Summary = "Transport a checked finite-prefix contradiction to a global state lower bound in the leading-zero model class.")]
public static class ZeroAnchoredLRATDFAStateLowerBound
{
    [Claim("zero_anchored_prefix_refutation_global", Kind = ClaimKind.Theorem, Proven = true)]
    public static string GlobalExclusion()
        => ForAll("P", "e", "k", "E", "R",
            Implies(
                And(
                    Math("E : RefutationEncoding(PrefixModels(P,e,k))"),
                    Math("R : CheckedRefutation(E.formula)")),
                Math("GlobalModels(P,k) is empty")));

    [Claim("zero_anchored_exact_minimality", Kind = ClaimKind.Theorem, Proven = true)]
    public static string ExactMinimality()
        => ForAll("P", "m", "e",
            Implies(
                And(
                    Math("GlobalModel(P,m)"),
                    Math("CheckedRefutation(PrefixModels(P,e,m-1))")),
                Math("m is minimal for P")));
}
