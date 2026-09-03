using static StrataLint.Scribe;

namespace Blueprint.D5.S0.Automata;

[Node("D5/S0/Automata/TypedStableRightCongruence", Title = "Typed stable right congruence", Role = NodeRole.Theorem, Status = NodeStatus.Proved, Owner = "agent", Summary = "Expose the typed transition-stable quotient forced on every finite labeled prefix family by a typed partial DFAO realization.")]
public static class TypedStableRightCongruence
{
    [Claim("typed_stable_right_congruence", Kind = ClaimKind.Definition, Proven = true)]
    public static string Definition()
        => Trait("StableRightCongruence",
            "same prefix words have one color",
            "every color has the certified base-automaton type",
            "equal-color parents have equal-color children under a shared observed symbol",
            "equal-color leaves have equal outputs");

    [Claim("identification_forgets_to_stable_congruence", Kind = ClaimKind.Theorem, Proven = true)]
    public static string ForgetfulMap()
        => ForAll("I",
            Implies(
                Math("Identification(I)"),
                Math("StableRightCongruence(forget(I))")));

    [Claim("stable_congruence_refutation_excludes_identification", Kind = ClaimKind.Theorem, Proven = true)]
    public static string RefutationBoundary()
        => ForAll("S", "B", "C",
            Implies(
                Math("not Nonempty(StableRightCongruence(S,B,C))"),
                Math("not Nonempty(Identification(S,B,C))")));
}
