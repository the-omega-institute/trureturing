using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class ScaledReversionCongruenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/ScaledReversionCongruence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scaled reversion proves Hanna's coefficient congruences in OEIS A393856 and A393857.",
        H("Scaled Reversion and Coefficient Congruence"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's entries hanna2026a393856 and hanna2026a393857 "
                + "specify A(x-x*A(q*x)/q)=x for q=4 and q=5 and conjecture that every "
                + "positive-index coefficient is one modulo q+1. The theorem below treats "
                + "every positive natural q. The separate parity conjecture in A393856 "
                + "is not addressed.")),
            Paragraph(Text("PowerSeries(R) denotes formal power series over R, X is the "
                + "indeterminate, coeff(n,f) extracts coefficient n, and mk builds a series "
                + "from its coefficient function. The notation subst(f,g) means f composed "
                + "with g. The constant-series embedding is C; rescale(r,f) multiplies "
                + "coefficient n by r to the power n. All indices and q are natural numbers. "
                + "Sequence values and the final remainders are integers. In the formulas "
                + "G(q) denotes generatingSeries(q), and P denotes the auxiliary iteration "
                + "specified with the definition of a.")),
            Node("a", "Stabilized integer coefficients", CoefficientFormula(),
                "Starting with the zero series, the correction P+X-subst(P,inner(q,P)) "
                + "gains one degree of agreement at each iteration. Coefficient n is read "
                + "at iteration n+1, where it has stabilized.", DescribeRole.Definition),
            Node("generatingSeries", "The integer generating series", GeneratingFormula(),
                "The coefficient function a(q) defines G(q) over the integers.",
                DescribeRole.Definition),
            Node("inner", "The integral inner argument", InnerFormula(),
                "The coefficient of degree n+2 subtracted from X is q to the power n "
                + "times coefficient n+1 of f. This expression is integral and its constant "
                + "and linear coefficients are zero and one, respectively.", DescribeRole.Definition),
            Node("generating_equation", "Existence and the rescaling identity", EquationFormula(),
                "Agreement with arbitrarily late approximations proves the substitution "
                + "equation. The first two coefficients follow from the initial iterations. "
                + "The last conjunct identifies the inner argument by clearing the scalar "
                + "denominator q; all four identities hold even at q=0."),
            Node("generating_unique", "Uniqueness by first difference", UniqueFormula(),
                "If two series agree below degree d, their inner arguments agree below "
                + "d+1. Substitution into a series beginning with X preserves the first "
                + "nonzero coefficient of their difference. The correction therefore "
                + "improves agreement by one degree. Induction proves uniqueness; no "
                + "constant-coefficient assumption on f is needed."),
            Node("generating_equation_rational", "The functional equation with division by q",
                RationalEquationFormula(),
                "Map the integer equation to rational coefficients. For positive q, "
                + "multiplication by its reciprocal converts the rescaling identity into "
                + "the displayed inner argument. Thus the constructed series satisfies "
                + "exactly A(x-x*A(q*x)/q)=x."),
            Node("coeff_congruence", "The parametric congruence", CongruenceFormula(),
                "Reduce the proved integer equation to ZMod(q+1), where q=-1. The series "
                + "E=X/(1-X) has inner argument X/(1+X), and substituting this into E "
                + "gives X. These identities follow by multiplying by unit denominators. "
                + "The first-difference uniqueness proof works over every commutative "
                + "ring, including ZMod(q+1), so the reduced generating series equals E. "
                + "Its positive-degree coefficients are one. Since q+1 is at least two, "
                + "one is the integer remainder."),
            Node("hanna_a393856", "The A393856 conjecture", SpecializationFormula(4, 5),
                "Specializing the parametric theorem to q=4 proves the mod-five conjecture "
                + "in hanna2026a393856 for every positive index.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Arith/hanna2026a393856")),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a393856-scaled-reversion-mod-five"),
                    ResolutionKind.Proved)),
            Node("hanna_a393857", "The A393857 conjecture", SpecializationFormula(5, 6),
                "Specializing the parametric theorem to q=5 proves the mod-six conjecture "
                + "in hanna2026a393857 for every positive index.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Arith/hanna2026a393857")),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a393857-scaled-reversion-mod-six"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("scaled-reversion-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Q() => F.Id("q");
    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula X() => F.Id("X");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
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
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula Positive(Formula value) => Seq(D(1), Sp, Le, Sp, value);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Function(string name, Formula body) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, Naturals(), Sp, Mapsto, Sp, body));
    private static Formula G() => Call("G", Q());
    private static Formula P(Formula count) => Call("P", Q(), count);
    private static Formula Inner(Formula series) => Call("inner", Q(), series);
    private static Formula CastQ(Formula ring) => Call("cast", Q(), ring);

    private static Formula CoefficientFormula() => Disp(new Formula.Aligned([
        Seq(Bound("q", Naturals()), Bound("n", Naturals()),
            Equal(Call("a", Q(), N()), Call("coeff", N(), P(Add(N(), D(1)))))),
        Seq(Bound("q", Naturals()), Equal(P(D(0)), D(0))),
        Seq(Bound("q", Naturals()), Bound("k", Naturals()),
            Equal(P(Add(K(), D(1))), Subtract(Add(P(K()), X()),
                Call("subst", P(K()), Inner(P(K()))))))
    ]));

    private static Formula GeneratingFormula() => Disp(Seq(Bound("q", Naturals()),
        Equal(G(), Call("mk", Call("a", Q())))));

    private static Formula InnerFormula() => Disp(Seq(Bound("q", Naturals()),
        Bound("f", Call("PowerSeries", Integers())),
        Equal(Inner(F.Id("f")), Subtract(X(), Mul(Power(X(), D(2)),
            Call("mk", Function("n", Mul(Power(CastQ(Integers()), N()),
                Call("coeff", Add(N(), D(1)), F.Id("f"))))))))));

    private static Formula EquationFormula() => Disp(new Formula.Aligned([
        Bound("q", Naturals()),
        And(Equal(Call("subst", G(), Inner(G())), X()),
            And(Equal(Call("constantCoeff", G()), D(0)),
                And(Equal(Call("coeff", D(1), G()), D(1)),
                    Equal(Mul(Call("C", CastQ(Integers())), Parenthesized(Subtract(X(), Inner(G())))),
                        Mul(X(), Call("rescale", CastQ(Integers()), G()))))))
    ]));

    private static Formula UniqueFormula() => Disp(Seq(Bound("q", Naturals()),
        Bound("f", Call("PowerSeries", Integers())),
        Implication(Equal(Call("subst", F.Id("f"), Inner(F.Id("f"))), X()),
            Equal(F.Id("f"), G()))));

    private static Formula RationalEquationFormula()
    {
        Formula series = F.Id("A");
        Formula reciprocal = Power(CastQ(Rationals()), Seq(Minus, D(1)));
        Formula argument = Subtract(X(), Mul(Mul(Call("C", reciprocal), X()),
            Call("rescale", CastQ(Rationals()), series)));
        return Disp(Seq(Bound("q", Naturals()), Implication(Positive(Q()),
            Seq(Named("let"), Sp, Equal(series,
                    Call("map", Call("intCastRingHom", Rationals()), G())), Comma, Sp,
                Equal(Call("subst", series, argument), X())))));
    }

    private static Formula CongruenceFormula() => Disp(Seq(Bound("q", Naturals()),
        Implication(Positive(Q()), Seq(Bound("n", Naturals()), Implication(Positive(N()),
            Equal(new Formula.Modulo(Call("a", Q(), N()), Parenthesized(Add(Q(), D(1)))), D(1)))))));

    private static Formula SpecializationFormula(byte parameter, byte modulus) =>
        Disp(Seq(Bound("n", Naturals()), Implication(Positive(N()),
            Equal(new Formula.Modulo(Call("a", D(parameter), N()), D(modulus)), D(1)))));
}
