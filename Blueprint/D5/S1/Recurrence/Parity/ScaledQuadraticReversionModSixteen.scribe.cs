using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class ScaledQuadraticReversionModSixteenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/ScaledQuadraticReversionModSixteen.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a396844");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized series of OEIS A396844 has alternating dyadic residues modulo sixteen.",
        H("Scaled Quadratic Reversion Modulo Sixteen"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2026a396844 specifies "
                + "A(x*A(x)-4*x*A(x)^2)=x^2 with A(x)=x+.... Its conjecture says that "
                + "above index eight the residue is twelve exactly at indices 2*4^k+1, "
                + "and that every other coefficient is divisible by sixteen.")),
            Paragraph(Text("All indices and exponents are natural numbers, and all "
                + "coefficients are integers. A denotes generatingSeries in PowerSeries(Z), "
                + "and X is its indeterminate. The operator subst(F,U) substitutes U into F; "
                + "coeff(n,F) extracts the nth coefficient; mk constructs a series from a "
                + "coefficient function. The operator map uses the displayed ring homomorphism; "
                + "IntCast(ZMod(m)) denotes Int.castRingHom into ZMod(m). "
                + "Remainders are integer remainders. B, F, P, C and q in the construction "
                + "below name its private unit part, factor, step, approximations and "
                + "stabilized coefficient function, respectively.")),
            Node("generatingSeries", "The integral construction", ConstructionFormula(),
                "The normalized form is A=X+X^2*mk(q). If two inputs to P agree below "
                + "degree d, their outputs agree below degree d+1: B gains one degree "
                + "through multiplication by X, and the substituted term has an outer "
                + "factor X. Thus coefficient n stabilizes after n+1 iterations. "
                + "This gives an integral fixed point without division.", DescribeRole.Definition),
            Node("a", "The coefficient sequence", CoefficientFormula(),
                "The value a(n) is the integer coefficient of degree n in A.",
                DescribeRole.Definition),
            Node("generating_equation", "The functional equation and normalization", EquationFormula(),
                "For A=X+X^2*c, the inner argument is X^2*F(c). Expanding the "
                + "composition gives X^2+X^3*(c-P(c)). The stabilized fixed point "
                + "therefore satisfies the OEIS equation, with constant coefficient "
                + "zero and linear coefficient one."),
            Node("generating_unique", "Uniqueness over the integers", UniqueFormula(),
                "Every series with the two normalization conditions has a unique "
                + "form X+X^2*c. Cancellation of X^3 turns its functional equation "
                + "into c=P(c). Induction on the agreement degree proves that any "
                + "two fixed points coincide."),
            Node("mod_four_identity", "Reduction modulo four",
                Disp(Equal(Call("map", Call("IntCast", Call("ZMod", D(4))), A()), X())),
                "Mapping the fixed-point equation to ZMod(4) makes c=0 a solution. "
                + "The same degree-contraction uniqueness gives c=0 and hence A=X."),
            Node("mod_sixteen_classification", "The corrected classification", ClassificationFormula(),
                "Let R be inverseSeries from AlternatingDyadicReversionModFour. Its "
                + "inverse_equation is R+R(X^2)=X. Write R=X*T; then "
                + "T+X*T(X^2)=1. Over ZMod(16), multiplication by four annihilates "
                + "each perturbation in B(4*T) and F(4*T). An annihilated difference "
                + "of substitution arguments remains annihilated after taking powers "
                + "and then after substitution. These facts show P(4*T)=4*T. "
                + "Uniqueness gives A=X+4*X*R modulo sixteen. Coefficient induction "
                + "in R+R(X^2)=X gives coefficient (-1)^k at degree 2^k and zero "
                + "elsewhere, proving all three biconditionals."),
            Node("hannaClaim", "The literature conjecture as a closed proposition", ClaimFormula(),
                "This proposition quantifies over every natural index greater than "
                + "eight. It includes both the residue-twelve biconditional and the "
                + "divisibility assertion at all remaining indices.", DescribeRole.Definition),
            Node("hanna_conjecture_false", "Refutation of the literature conjecture",
                Disp(Seq(Neg, Sp, Call("hannaClaim"))),
                "The literature conjecture in hanna2026a396844 is refuted. The corrected "
                + "classification holds for every n at least two: residue four occurs "
                + "exactly at n=2^k+1 with even k, residue twelve exactly with odd k, "
                + "and divisibility by sixteen exactly off this support. In particular, "
                + "17=2^4+1 has residue four by the symbolic classification. Since "
                + "17 is not 2*4^k+1 for any natural k, the conjecture would require "
                + "sixteen to divide a(17), a contradiction.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396844-scaled-quadratic-reversion-mod-sixteen"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a396844-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula A() => F.Id("A");
    private static Formula X() => F.Id("X");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula first, Formula second) =>
        Seq(Parenthesized(first), Sp, Land, Sp, Parenthesized(second));
    private static Formula Biconditional(Formula first, Formula second) =>
        Seq(Parenthesized(first), Sp, Iff, Sp, Parenthesized(second));
    private static Formula Divides(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, right);
    private static Formula Not(Formula value) => Seq(Neg, Sp, Parenthesized(value));
    private static Formula Equation(Formula b) => Equal(Call("subst", b,
        Parenthesized(Subtract(Mul(X(), b), Mul(Mul(D(4), X()), Power(b, D(2)))))),
        Power(X(), D(2)));

    private static Formula ConstructionFormula()
    {
        Formula c = F.Id("c");
        Formula n = F.Id("n");
        Formula b = Call("B", c);
        Formula f = Call("F", c);
        return Disp(new Formula.Aligned([
            Seq(Bound("c", Series()), Equal(b, Add(D(1), Mul(X(), c)))),
            Seq(Bound("c", Series()), Equal(f, Mul(b,
                Parenthesized(Subtract(D(1), Mul(Mul(D(4), X()), b)))))),
            Seq(Bound("c", Series()), Equal(Call("P", c), Subtract(
                Mul(D(4), Power(b, D(2))), Mul(X(), Parenthesized(Mul(Power(f, D(2)),
                    Call("subst", c, Mul(Power(X(), D(2)), f)))))))),
            Equal(Call("C", D(0)), D(0)),
            Seq(Bound("n", Naturals()), Equal(Call("C", Add(n, D(1))), Call("P", Call("C", n)))),
            Seq(Bound("n", Naturals()), Equal(Call("q", n),
                Call("coeff", n, Call("C", Add(n, D(1)))))),
            Equal(A(), Add(X(), Mul(Power(X(), D(2)), Call("mk", F.Id("q")))))
        ]));
    }

    private static Formula CoefficientFormula() => Disp(Seq(Bound("n", Naturals()),
        Equal(Call("a", F.Id("n")), Call("coeff", F.Id("n"), A()))));

    private static Formula EquationFormula() => Disp(Conjunction(
        Equal(Call("constantCoeff", A()), D(0)), Conjunction(
            Equal(Call("coeff", D(1), A()), D(1)), Equation(A()))));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Call("constantCoeff", b), D(0)),
                Implication(Equal(Call("coeff", D(1), b), D(1)),
                    Implication(Equation(b), Equal(b, A()))))));
    }

    private static Formula Support(Formula n, string? parity = null, bool literature = false)
    {
        Formula k = F.Id("k");
        Formula index = literature ? Add(Mul(D(2), Power(D(4), k)), D(1))
            : Add(Power(D(2), k), D(1));
        Formula body = Equal(n, index);
        if (parity is not null) body = Conjunction(Call(parity, k), body);
        return Seq(Exists, Sp, k, Colon, Sp, Naturals(), Comma, Sp, Parenthesized(body));
    }

    private static Formula ClassificationFormula()
    {
        Formula n = F.Id("n");
        Formula remainder = new Formula.Modulo(Call("a", n), D(1, 6));
        Formula body = Conjunction(
            Biconditional(Equal(remainder, D(4)), Support(n, "Even")), Conjunction(
                Biconditional(Equal(remainder, D(1, 2)), Support(n, "Odd")),
                Biconditional(Divides(D(1, 6), Call("a", n)), Not(Support(n)))));
        return Disp(Seq(Bound("n", Naturals()),
            Implication(Seq(D(2), Sp, Le, Sp, n), Parenthesized(body))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n");
        Formula support = Support(n, literature: true);
        Formula body = Conjunction(Biconditional(
            Equal(new Formula.Modulo(Call("a", n), D(1, 6)), D(1, 2)), support),
            Implication(Not(support), Divides(D(1, 6), Call("a", n))));
        return Disp(Biconditional(Call("hannaClaim"), Seq(Bound("n", Naturals()),
            Implication(Seq(D(8), Sp, Lt, Sp, n), Parenthesized(body)))));
    }
}
