using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class DoubleCompositionModFourClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/DoubleCompositionModFourClassification.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2024a372577");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized series of OEIS A372577 has a complete modulo-four classification.",
        H("Hanna's Double-Composition Modulo-Four Classification"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2024a372577 defines A(x) by "
                + "A(x)^2=A(A(x*A(x)+x*A(x)^2)), with constant coefficient zero and "
                + "linear coefficient one. It conjectures remainder three at indices "
                + "6m-3 and remainder one at indices 6m-k for k in {0,1,2,4,5}, "
                + "where m is positive. These indices cover all positive integers.")),
            Paragraph(Text("PowerSeries(Z) denotes formal power series over the integers, "
                + "X is the indeterminate, coeff extracts a coefficient, and mk constructs "
                + "a series from its coefficient function. The notation subst(f,u) means "
                + "f(u), with the outer series first. All indices are natural numbers. "
                + "The remainder of n is natural remainder, and the remainder of a(n) "
                + "is integer remainder. The displayed approximation, argument, nested, "
                + "and step operations are local notation for the private construction.")),
            Node("generatingSeries", "Construction by stabilized coefficients", GeneratingFormula(),
                "Writing A=X*U and cancelling X^2*U gives U=step(U). Each substitution "
                + "argument is divisible by X^2. If two unit series agree below degree d, "
                + "where d is positive, their transformed series agree below degree d+1. "
                + "The approximations start at one, keep constant coefficient one, and "
                + "stabilize through degree d by approximation d. Their diagonal "
                + "coefficients define U and hence generatingSeries.", DescribeRole.Definition),
            Node("a", "The integer coefficient sequence", CoefficientFormula(),
                "The coefficient sequence is extracted from the constructed generating series.",
                DescribeRole.Definition),
            Node("generating_equation", "The double composition and normalization", EquationFormula(),
                "Coefficient stabilization proves that U is fixed by step. Multiplying "
                + "this fixed-point identity by X^2*U restores the two nested substitutions "
                + "in the defining equation. The constant and linear coefficients follow "
                + "from the factor X and the constant coefficient one of U."),
            Node("generating_unique", "Uniqueness of the normalized solution", UniqueFormula(),
                "Factor any competing solution as X*U. The linear normalization makes U "
                + "a unit, so cancelling X^2 and U in the equation gives the same fixed-point "
                + "identity. Degree contraction proves equality of all coefficients."),
            Node("hanna_conjecture", "Every positive coefficient modulo four", PatternFormula(),
                "Over ZMod(4), put P=X+X^2+3X^3+X^4+X^5+X^6 and D=1-X^6. "
                + "The rational series P/D satisfies the full double-composition equation: "
                + "homogenizing P and D clears each substitution denominator, and two "
                + "polynomial identities establish the result by unit cancellation. "
                + "Uniqueness identifies it with the reduction of generatingSeries. "
                + "The identity P/D=X/(1-X)+2X^3/(1-X^6), with formal unit inverses, "
                + "then gives remainder three precisely at n mod 6 equal to three, and "
                + "remainder one otherwise. This is both conjectured clauses together.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a372577-double-composition-mod-four"),
                    ResolutionKind.Proved)),
            Node("odd_coefficients", "Oddness as a corollary", OddFormula(),
                "The complete classification gives only the residues one and three "
                + "modulo four. Both imply integer remainder one modulo two, so every "
                + "positive-index coefficient is odd."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a372577-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula SeriesType() => Call("PowerSeries", Integers());
    private static Formula X() => F.Id("X");
    private static Formula N() => F.Id("n");
    private static Formula A() => Named("generatingSeries");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) => Seq(left, Sp, Plus, Sp, right);
    private static Formula Mul(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Cdot, Sp, Parenthesized(right));
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Positive() => Seq(D(0), Sp, Lt, Sp, N());
    private static Formula Approx(Formula depth) => Call("approximation", depth);
    private static Formula Argument(Formula series) => Call("argument", series);
    private static Formula Nested(Formula series) => Call("nested", series);
    private static Formula Substitution(Formula outer, Formula inner) => Call("subst", outer, inner);
    private static Formula Step(Formula series) =>
        Mul(Mul(Add(D(1), Mul(X(), series)), Substitution(series, Argument(series))),
            Substitution(series, Nested(series)));
    private static Formula Equation(Formula series) => Equal(Power(series, D(2)),
        Substitution(series, Substitution(series,
            Add(Mul(X(), series), Mul(X(), Power(series, D(2)))))));

    private static Formula GeneratingFormula()
    {
        var f = F.Id("f");
        return Disp(new Formula.Aligned([
            Equal(A(), Mul(X(), Call("mk", Parenthesized(Seq(
                N(), Colon, Sp, Naturals(), Sp, Mapsto, Sp,
                Call("coeff", N(), Approx(N()))))))),
            Equal(Approx(D(0)), D(1)),
            Seq(Bound("d", Naturals()), Equal(Approx(Add(F.Id("d"), D(1))),
                Call("step", Approx(F.Id("d"))))),
            Seq(Bound("f", SeriesType()), Equal(Call("step", f), Step(f))),
            Seq(Bound("f", SeriesType()), Equal(Argument(f),
                Mul(Mul(Power(X(), D(2)), f), Add(D(1), Mul(X(), f))))),
            Seq(Bound("f", SeriesType()), Equal(Nested(f),
                Mul(Argument(f), Substitution(f, Argument(f)))))
        ]));
    }

    private static Formula CoefficientFormula() => Disp(Seq(Bound("n", Naturals()),
        Equal(Call("a", N()), Call("coeff", N(), A()))));

    private static Formula EquationFormula() => Disp(And(
        Equal(Call("constantCoeff", A()), D(0)), And(
            Equal(Call("coeff", D(1), A()), D(1)), Equation(A()))));

    private static Formula UniqueFormula()
    {
        var f = F.Id("f");
        return Disp(Seq(Bound("f", SeriesType()),
            Implication(Equal(Call("constantCoeff", f), D(0)),
                Implication(Equal(Call("coeff", D(1), f), D(1)),
                    Implication(Equation(f), Equal(f, A()))))));
    }

    private static Formula PatternFormula()
    {
        var pattern = Parenthesized(Seq(Named("if"), Sp,
            Parenthesized(Equal(new Formula.Modulo(N(), D(6)), D(3))), Sp,
            Named("then"), Sp, D(3), Sp, Named("else"), Sp, D(1)));
        return Disp(Seq(Bound("n", Naturals()), Implication(Positive(),
            Equal(new Formula.Modulo(Call("a", N()), D(4)), pattern))));
    }

    private static Formula OddFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Positive(), Call("Odd", Call("a", N())))));
}
