using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class SubstitutionSquareCubeModFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/SubstitutionSquareCubeModFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2025a389536");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized coefficients of OEIS A389536 are two modulo four exactly at powers of two plus one.",
        H("Hanna's Square-Cube Substitution Conjecture"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2025a389536 defines A(x) by "
                + "A(x)=A(x^2+2x^3)/x and conjectures its coefficient pattern modulo four. "
                + "We use the equivalent formal power-series identity xA(x)=A(x^2+2x^3), "
                + "with zero constant term and a(1)=1. Comparing degree two gives "
                + "a(1)=a(1), so the first coefficient is a free normalization.")),
            Paragraph(Text("All indices and exponents are natural numbers. Fin(n) consists "
                + "of the indices k with 0<=k<n; its elements are read as natural numbers "
                + "in coefficients and exponents. Subtraction in indices is natural subtraction. "
                + "The values of a and the displayed binomial coefficients in products are "
                + "integers. PowerSeries(Z) is the formal power-series ring with indeterminate X. "
                + "The notation subst(B,Q) means B composed with Q, coeff(n,B) is coefficient n, "
                + "and mk(a) constructs the series with coefficient function a. Remainders "
                + "in the final theorem are integer remainders.")),
            Node("a", "The normalized coefficient sequence", SequenceFormula(),
                "The recursion only uses indices smaller than n+2 and therefore defines "
                + "an integer sequence without assuming existence of a solution to the equation.",
                DescribeRole.Definition),
            Node("generatingSeries", "The generating series", GeneratingFormula(),
                "The coefficient of index n in generatingSeries is a(n).",
                DescribeRole.Definition),
            Node("generating_equation", "The normalized functional equation", EquationFormula(),
                "The kth power of X^2+2X^3 has no coefficients below degree 2k. "
                + "Consequently each substituted coefficient is a finite sum, and the "
                + "defining recursion gives the equation coefficient by coefficient. "
                + "The constant and linear coefficients supply the two normalizations."),
            Node("generating_unique", "Uniqueness of the normalized solution", UniqueFormula(),
                "For n at least two, coefficient n+1 of the equation determines coefficient n "
                + "using only smaller indices. Strong induction, with the prescribed constant "
                + "and linear coefficients as initial cases, proves uniqueness."),
            Node("coeff_recurrence", "The binomial coefficient bridge", RecurrenceFormula(),
                "Extract coefficient n+1 from the proved generating equation. Factor the "
                + "kth substituted power as X^(2k)(1+2X)^k and apply the binomial coefficient "
                + "formula. The inequality in the summand excludes degrees below 2k."),
            Node("a_even", "Evenness beyond the normalized term", EvenFormula(),
                "Modulo four only exponents zero and one in the binomial expansion survive. "
                + "Thus a(2m-1) is congruent to a(m) for m>=2, and a(2m) is congruent to "
                + "2m a(m) for m>=1. Reducing these relations modulo two and applying strong "
                + "induction proves evenness for every index at least two."),
            Node("hanna_conjecture", "The complete A389536 conjecture", ConjectureFormula(),
                "The even-index contraction and evenness give remainder zero at every even "
                + "index at least four, while index two has remainder two. The odd-index "
                + "contraction preserves the remainder and transforms m=2^k+1 into "
                + "2m-1=2^(k+1)+1. Strong induction proves the first equivalence. Evenness "
                + "leaves only remainders zero and two, giving the complementary equivalence.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a389536-substitution-square-cube-mod-four"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a389536-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula X() => F.Id("X");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula Generating() => Named("generatingSeries");
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
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Inner() => Add(Power(X(), D(2)), Mul(D(2), Power(X(), D(3))));
    private static Formula Coefficient(Formula index, Formula series) => Call("coeff", index, series);
    private static Formula A(Formula index) => Call("a", index);
    private static Formula SumFin(Formula bound, Formula summand) =>
        Seq(new Formula.Subscript(F.Sum, Seq(K(), Colon, Sp, Call("Fin", bound))),
            Sp, Parenthesized(summand));
    private static Formula Equation(Formula series) =>
        Equal(Mul(X(), series), Call("subst", series, Inner()));

    private static Formula SequenceFormula() => Disp(new Formula.Aligned([
        Seq(Named("a"), Colon, Sp, Naturals(), Sp, To, Sp, Integers()),
        Equal(A(D(0)), D(0)),
        Equal(A(D(1)), D(1)),
        Seq(Bound("n", Naturals()), Equal(A(Add(N(), D(2))),
            SumFin(Add(N(), D(2)), Mul(A(K()),
                Coefficient(Add(N(), D(3)), Power(Parenthesized(Inner()), K()))))))
    ]));

    private static Formula GeneratingFormula() => Disp(Seq(
        Generating(), Colon, Sp, Series(), Comma, Sp,
        Equal(Generating(), Call("mk", Named("a")))));

    private static Formula EquationFormula() => Disp(Conjunction(
        Equal(Call("constantCoeff", Generating()), D(0)),
        Conjunction(Equal(Coefficient(D(1), Generating()), D(1)), Equation(Generating()))));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Call("constantCoeff", b), D(0)),
                Implication(Equal(Coefficient(D(1), b), D(1)),
                    Implication(Equation(b), Equal(b, Generating()))))));
    }

    private static Formula RecurrenceFormula()
    {
        Formula degree = Subtract(Add(N(), D(1)), Mul(D(2), K()));
        Formula summand = Seq(Named("if"), Sp,
            Parenthesized(Seq(Mul(D(2), K()), Sp, Le, Sp, Add(N(), D(1)))), Sp,
            Named("then"), Sp,
            Mul(Mul(A(K()), Power(D(2), degree)), Call("choose", K(), degree)), Sp,
            Named("else"), Sp, D(0));
        return Disp(Seq(Bound("n", Naturals()),
            Implication(Seq(D(2), Sp, Le, Sp, N()), Equal(A(N()), SumFin(N(), summand)))));
    }

    private static Formula EvenFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(2), Sp, Le, Sp, N()), Seq(D(2), Sp, Mid, Sp, A(N())))));

    private static Formula PowerIndex() => Seq(Exists, Sp, K(), Colon, Sp, Naturals(), Comma, Sp,
        Equal(N(), Add(Power(D(2), K()), D(1))));

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Lt, Sp, N()), Conjunction(
            Seq(Parenthesized(Equal(new Formula.Modulo(A(N()), D(4)), D(2))), Sp, Iff, Sp,
                Parenthesized(PowerIndex())),
            Seq(Parenthesized(Equal(new Formula.Modulo(A(N()), D(4)), D(0))), Sp, Iff, Sp,
                Neg, Sp, Parenthesized(PowerIndex()))))));
}
