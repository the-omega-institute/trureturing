using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class AbsoluteReciprocalGeometricParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/AbsoluteReciprocalGeometricParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2025a383377");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every coefficient of OEIS A383377 above index one is even.",
        H("Hanna's Absolute Reciprocal Geometric Parity"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2025a383377 defines A(x) as the sum "
                + "of x^n times the coefficientwise absolute value of its nth reciprocal "
                + "power, and conjectures evenness for n greater than one. The integer "
                + "series below is constructed and proved to satisfy that equation uniquely "
                + "among series with constant coefficient one.")),
            Paragraph(Text("All indices are natural numbers. PowerSeries(Z) denotes integer "
                + "formal power series, X is its indeterminate, coeff(N,F) is coefficient N, "
                + "and mk constructs a series from a coefficient function. The operation "
                + "invOfUnit(F,1) is the unit inverse when the constant coefficient is one; "
                + "powers are ordinary products of series. The symbol abs denotes integer "
                + "absolute value. Each coefficient sum is finite: terms indexed above N "
                + "contain X to a power greater than N and contribute zero at degree N. "
                + "The map intCast(ZMod(2)) denotes Int.castRingHom(ZMod(2)); map(h,F) "
                + "applies h to every coefficient of F.")),
            Node("absSeries", "Coefficientwise absolute value", AbsoluteFormula(),
                "The coefficient function is replaced by its integer absolute value.",
                DescribeRole.Definition),
            Node("a", "Stabilized integer coefficients", CoefficientFormula(),
                "The auxiliary approximation starts at one. Each successor is formed by "
                + "the displayed finite coefficient sums. The transformation preserves "
                + "constant coefficient one and improves agreement below d to agreement "
                + "below d+1. Consequently coefficient n has stabilized by approximation n+1.",
                DescribeRole.Definition),
            Node("generatingSeries", "The generating series", GeneratingFormula(),
                "The generating series has the integer coefficient function a.",
                DescribeRole.Definition),
            Node("generating_equation", "The exact defining equation", EquationFormula(),
                "Agreement with sufficiently late approximations, followed by one more "
                + "degree contraction, proves both the constant coefficient and every "
                + "coefficient equation. The finite-sum form is the defining formal "
                + "generating-function equation from hanna2025a383377."),
            Node("generating_unique", "Uniqueness of the normalized solution", UniqueFormula(),
                "For two series with constant coefficient one, taking unit inverses "
                + "preserves coefficient agreement below any degree. Powers and absolute "
                + "values preserve it as well. Every nonconstant summand then gains a "
                + "factor X. Induction gives agreement at every degree, proving equality."),
            Node("mod_two_identity", "The entire series modulo two", ModTwoFormula(),
                "Integer absolute value disappears modulo two. Write F for the mapped "
                + "series and U for its mapped unit inverse, so UF=1. The coefficient "
                + "equation makes F agree below d with the sum of (XU)^n for n below d. "
                + "Multiplication by 1-XU and finite geometric cancellation yield "
                + "F(1-XU)=1 at every degree. Since FXU=X, this gives F=1+X."),
            Node("hanna_conjecture", "The A383377 parity conjecture", ParityFormula(),
                "Taking coefficient n in the modulo-two identity gives zero whenever "
                + "n is greater than one. The integer cast criterion for ZMod(2) converts "
                + "this vanishing to Even(a(n)).", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a383377-absolute-reciprocal-geometric-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a383377-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula X() => F.Id("X");
    private static Formula N() => F.Id("N");
    private static Formula SmallN() => F.Id("n");
    private static Formula Generating() => Named("generatingSeries");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Lambda(string name, Formula body) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, Naturals(), Sp, Mapsto, Sp, body));
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Coefficient(Formula index, Formula series) => Call("coeff", index, series);
    private static Formula Approx(Formula depth) => Call("approximation", depth);
    private static Formula ConstantOne(Formula series) => Equal(Call("constantCoeff", series), D(1));

    private static Formula CoefficientSum(Formula series, Formula index) => Seq(
        new Formula.Subscript(F.Sum, Seq(SmallN(), Sp, InMacro, Sp,
            Call("range", Add(index, D(1))))), Sp,
        Parenthesized(Coefficient(index, Mul(Power(X(), SmallN()),
            Call("absSeries", Power(Call("invOfUnit", series, D(1)), SmallN()))))));

    private static Formula CoefficientEquation(Formula series) => Seq(Bound("N", Naturals()),
        Equal(Coefficient(N(), series), CoefficientSum(series, N())));

    private static Formula AbsoluteFormula() => Disp(Seq(Bound("F", Series()),
        Equal(Call("absSeries", F.Id("F")), Call("mk", Lambda("n",
            Call("abs", Coefficient(SmallN(), F.Id("F"))))))));

    private static Formula CoefficientFormula() => Disp(new Formula.Aligned([
        Equal(Approx(D(0)), D(1)),
        Seq(Bound("d", Naturals()), Equal(Approx(Add(F.Id("d"), D(1))),
            Call("mk", Lambda("N", CoefficientSum(Approx(F.Id("d")), N()))))),
        Seq(Bound("n", Naturals()), Equal(Call("a", SmallN()),
            Coefficient(SmallN(), Approx(Add(SmallN(), D(1))))))
    ]));

    private static Formula GeneratingFormula() => Disp(Equal(Generating(), Call("mk", Named("a"))));

    private static Formula EquationFormula() => Disp(
        Conjunction(ConstantOne(Generating()), CoefficientEquation(Generating())));

    private static Formula UniqueFormula() => Disp(Seq(Bound("B", Series()),
        Implication(ConstantOne(F.Id("B")), Implication(CoefficientEquation(F.Id("B")),
            Equal(F.Id("B"), Generating())))));

    private static Formula ModTwoFormula() => Disp(Equal(
        Call("map", Call("intCast", Call("ZMod", D(2))), Generating()), Add(D(1), X())));

    private static Formula ParityFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Lt, Sp, SmallN()), Call("Even", Call("a", SmallN())))));
}
