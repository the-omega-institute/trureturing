using static StrataLint.Scribe;

namespace Blueprint.D5.S0.Certificates;

[Node("D5/S0/Certificates/DFAIdentificationCNF", Title = "Certified DFA-identification CNF", Role = NodeRole.Theorem, Status = NodeStatus.Proved, Owner = "agent", Summary = "Separate refutation-only completeness from exact SAT-to-machine decoding for finite DFA-identification formulas.")]
public static class DFAIdentificationCNF
{
    [Claim("M05R_refutation_encoding", Kind = ClaimKind.Definition, Proven = true)]
    public static string RefutationEncoding()
        => Class("RefutationEncoding",
            "Problem",
            Field("formula", "Sat.Fmla"),
            Field("complete", "Problem -> Satisfiable(formula)"));

    [Claim("M05E_exact_encoding", Kind = ClaimKind.Definition, Proven = true)]
    public static string ExactEncoding()
        => Class("CertifiedEncoding",
            "Problem",
            Field("formula", "Sat.Fmla"),
            Field("sound", "Satisfiable(formula) -> Problem"),
            Field("complete", "Problem -> Satisfiable(formula)"));

    [Claim("M05_exact_semantics", Kind = ClaimKind.Theorem, Proven = true)]
    public static string ExactSemantics()
        => ForAll("P", "E",
            Implies(
                Math("E : CertifiedEncoding(P)"),
                Iff(
                    Math("Satisfiable(E.formula)"),
                    Math("P"))));

    [Claim("M05_stable_congruence_refutation", Kind = ClaimKind.Theorem, Proven = true)]
    public static string StableCongruenceRefutation()
        => ForAll("S", "B", "C", "E",
            Implies(
                Math("E : RefutationEncoding(StableRightCongruence(S,B,C))"),
                Math("E also encodes Identification(S,B,C) for refutation")));
}
