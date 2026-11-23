using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel;

internal sealed class MakowskiSchinzelMainDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Divisors/MakowskiSchinzel/Main.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/makowskischinzel1964totient");
    private static readonly LibraryNoteRef Cohen =
        LibraryNoteRef.Create("D5/L/ArithUnits/cohen1997makowski");
    private static readonly LibraryNoteRef Pomerance =
        LibraryNoteRef.Create("D5/L/ArithUnits/pomerance2026makowski");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sigma-totient inequality for eta at most forty-two",
        H("The sigma-totient inequality for eta at most forty-two"), Blocks(
            Node("lift_odd_squarefree_iff", "The exact odd squarefree reduction", GeneralLift(),
                "For a predicate P closed under taking the odd squarefree core of a " +
                "nonzero integer, the inequality alpha(m)>=1 on odd squarefree inputs " +
                "satisfying P is equivalent to both sigma-totient bounds on all inputs " +
                "satisfying P. The core is the radical when odd, and half the radical " +
                "when even. No closure under other divisors is required. Both parity " +
                "cases are needed to apply the restricted bound to their respective " +
                "cores. Zero needs no closure assumption because both bounds vanish."),
            Node("lift_odd_squarefree", "Lifting from odd squarefree integers", Lift(),
                "A support-bounded inequality for odd squarefree integers implies the " +
                "factor-two inequality for all natural integers and the stronger " +
                "inequality for odd ones. Radical reduction removes all multiplicities; " +
                "adjoining a single factor of 2 halves the ratio. Zero is included " +
                "because both natural-number inequalities then have zero on both sides."),
            Node("odd_alpha_eta_le_42", "The stronger odd-integer inequality",
                All("n", Nat(), Imp(Call("Odd", V("n")),
                    Imp(Le(Call("eta", V("n")), D(4,2)),
                        Le(D(1), Call("alpha", V("n")))))),
                "Every odd n with at most forty-two distinct non-Fermat odd prime divisors " +
                "has alpha(n)>=1. The least odd prime divisor of the totient is either " +
                "excluded by the finite support inequalities or contradicted by the " +
                "geometric tail bound. A power-of-two totient is handled separately."),
            Node("makowski_schinzel_eta_le_42", "Both inequalities with unbounded multiplicity",
                MainStatement(),
                "For every natural n with eta(n)<=42, n<=2 sigma(phi(n)); when n is odd, " +
                "n<=sigma(phi(n)). Prime exponents are unrestricted, as are n and the " +
                "sizes of its prime factors. The natural-number convention includes zero. " +
                "Equality prevents universal strictness: n=2 gives equality in the " +
                "factor-two bound, and n=1 gives equality in the odd bound. This is the " +
                "support-bounded partial result toward the Mąkowski–Schinzel conjecture, " +
                "not its unrestricted settlement. The related numerical ranges " +
                "n<=10^60 and P(n)<10^6 belong to the cited preprint and are separate " +
                "from eta(n)<=42. They are not additional premises or conclusions."))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, bool definition = false) => Describe.Lean(
        DescribeId.Create("makowski-schinzel-main-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(Source, Cohen, Pomerance),
        Blocks(Paragraph(Text(prose))),
        definition ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula GeneralLift()
    {
        var n = V("n"); var m = V("m");
        var rad = Call("radical", n);
        var cores = Or(Eq(rad, m), Eq(rad, Mul(D(2), m)));
        var closed = All("n", Nat(), Imp(Ne(n, D(0)), Imp(Call("P", n),
            All("m", Nat(), Imp(Call("Odd", m), Imp(cores, Call("P", m)))))));
        var restricted = All("m", Nat(), Imp(Call("Odd", m), Imp(Call("Squarefree", m),
            Imp(Call("P", m), Le(D(1), Call("alpha", m))))));
        var sigma = Call("sigma", D(1), Call("totient", n));
        var bounds = All("n", Nat(), Imp(Call("P", n),
            And(Le(n, Mul(D(2), sigma)), Imp(Call("Odd", n), Le(n, sigma)))));
        return All("P", Call("Function", Nat(), Call("Prop")),
            Imp(closed, new Formula.Logic(restricted, FormulaLogicOperator.Iff, bounds)));
    }

    private static Formula Lift()
    {
        var t = V("T"); var n = V("n"); var m = V("m");
        var odd = All("m", Nat(), Imp(Call("Odd", m), Imp(Call("Squarefree", m),
            Imp(Le(Call("eta", m), t), Le(D(1), Call("alpha", m))))));
        var sigma = Call("sigma", D(1), Call("totient", n));
        var result = And(Le(n, Mul(D(2), sigma)), Imp(Call("Odd", n), Le(n, sigma)));
        return All("T", Nat(), Imp(odd, All("n", Nat(),
            Imp(Le(Call("eta", n), t), result))));
    }

    private static Formula MainStatement()
    {
        var n = V("n"); var sigma = Call("sigma", D(1), Call("totient", n));
        return All("n", Nat(), Imp(Le(Call("eta", n), D(4,2)),
            And(Le(n, Mul(D(2), sigma)), Imp(Call("Odd", n), Le(n, sigma)))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
