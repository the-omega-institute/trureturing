using static StrataLint.Scribe;

namespace Blueprint.D5.S0.Automata;

[Node("D5/S0/Automata/ZeroAnchoredSparseDFAO", Title = "Zero-anchored sparse DFAO semantics", Role = NodeRole.Definition, Status = NodeStatus.Proved, Owner = "agent", Summary = "Fix the base automaton, leading-zero symbol, zero output, and sparse target sequence inside the canonical typed partial-DFAO model class.")]
public static class ZeroAnchoredSparseDFAO
{
    [Claim("zero_anchored_sparse_problem", Kind = ClaimKind.Definition, Proven = true)]
    public static string Problem()
        => Class("Problem",
            "Alphabet", "Output", "BaseState",
            Field("base", "BaseAutomaton Alphabet BaseState"),
            Field("zero", "Alphabet"),
            Field("zeroOutput", "Output"),
            Field("input", "Nat -> List Alphabet"),
            Field("target", "Nat -> Output"));

    [Claim("zero_anchored_correctness", Kind = ClaimKind.Definition, Proven = true)]
    public static string Correct()
        => Because(
            "A correct machine matches the fixed base and zero symbol, outputs zeroOutput on the zero word, and realizes every sparse target.",
            Math("Correct(P,M)"));

    [Claim("zero_anchored_global_to_prefix", Kind = ClaimKind.Theorem, Proven = true)]
    public static string GlobalToPrefix()
        => ForAll("P", "e", "k",
            Implies(
                Math("P.HasGlobalModelAtMost(k)"),
                Math("P.HasPrefixModelAtMost(e,k)")));
}
