using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class AbsoluteReciprocalSquareParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/AbsoluteReciprocalSquareParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2025a380710");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive-index coefficients of OEIS A380710 are odd exactly at powers of two.",
        H("Absolute Reciprocal Squares and Binary Parity"),
        Blocks(
            Paragraph(Text("The generating equation and conjecture are recorded in "
                + "hanna2025a380710. Write A for generatingSeries and C for "
                + "CatalanCompositionSquareParity.catalanSeries. The series A, C, F, B, "
                + "and P(r) have integer coefficients, X is the indeterminate, and "
                + "all coefficient indices and exponents are natural numbers.")),
            Paragraph(Text("The operator mk forms a series from its coefficient function; "
                + "coeff(n,F) extracts its degree-n coefficient. The scalar operator abs "
                + "is integer absolute value. The operator invOfUnit(F,1) is Mathlib's "
                + "power-series inverse with the unit 1 as constant-coefficient parameter. "
                + "When the constant coefficient of F is one, its product with this "
                + "inverse is one. The operator map applies a ring homomorphism "
                + "coefficientwise, and intCast(ZMod(2)) denotes Int.castRingHom(ZMod(2)).")),
            Node("absSeries", "Coefficientwise absolute value", AbsoluteDefinition(),
                "The coefficient of absSeries(F) at each natural index n is the "
                + "integer absolute value of the corresponding coefficient of F.",
                DescribeRole.Definition),
            Node("a", "The stabilized coefficient sequence", SequenceDefinition(),
                "The displayed recursion defines the auxiliary approximations P(r). "
                + "The map gains one degree of coefficient agreement: powers, inverses "
                + "with constant coefficient one, and coefficientwise absolute values "
                + "preserve agreement, while multiplication by X shifts it. Thus "
                + "the degree-n coefficient stabilizes by approximation n+1.",
                DescribeRole.Definition),
            Node("generatingSeries", "The generating series",
                Disp(Equal(A(), Call("mk", Named("a")))),
                "The series A is formed from the stabilized integer coefficients a(n).",
                DescribeRole.Definition),
            Node("generating_equation", "The exact functional equation",
                Disp(Conjunction(Equal(Constant(A()), D(1)), Equation(A()))),
                "Coefficient stabilization makes A a fixed point of the approximation "
                + "map. Its constant coefficient is one, so the inverse in the "
                + "equation is the reciprocal of A squared."),
            Node("generating_unique", "Uniqueness of the normalized solution", UniqueFormula(),
                "Any integer solution B with constant coefficient one agrees with A "
                + "below degree zero. The fixed-point equations and degree contraction "
                + "extend agreement by one degree at every step, proving B=A."),
            Node("mod_two_identity", "Reduction to the shifted Catalan series",
                Disp(Equal(Reduce(A()), Add(D(1), Reduce(Catalan())))),
                "In ZMod(2), the images of an integer and its absolute value coincide. "
                + "Mapping the reciprocal-square identity and multiplying the defining "
                + "equation by the reduced series gives its square equal to itself plus X. "
                + "The frozen Catalan equation gives the same quadratic equation for "
                + "1+map(intCast(ZMod(2)),C). The difference of the two solutions is "
                + "annihilated by one minus their sum. This factor has unit constant "
                + "coefficient, so cancellation identifies the two solutions."),
            Node("hanna_conjecture", "Hanna's A380710 parity conjecture", ConjectureFormula(),
                "At a positive index, adding the constant series one changes no "
                + "coefficient. The reduction identity and the frozen binary_catalan "
                + "theorem therefore give odd a(n) exactly when n is a power of two.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a380710-absolute-reciprocal-square-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a380710-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula A() => F.Id("A");
    private static Formula X() => F.Id("X");
    private static Formula Catalan() => F.Id("C");
    private static Formula N() => F.Id("n");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Lambda(string name, Formula body) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, Naturals(), Sp, Mapsto, Sp, body));
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Coefficient(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula Constant(Formula f) => Call("constantCoeff", f);
    private static Formula Step(Formula f) => Add(D(1),
        Mul(Mul(X(), f), Call("absSeries", Call("invOfUnit", Power(f, D(2)), D(1)))));
    private static Formula Equation(Formula f) => Equal(f, Step(f));
    private static Formula Reduce(Formula f) =>
        Call("map", Call("intCast", Call("ZMod", D(2))), f);

    private static Formula AbsoluteDefinition() => Disp(Seq(Bound("F", Series()),
        Equal(Call("absSeries", F.Id("F")),
            Call("mk", Lambda("n", Call("abs", Coefficient(N(), F.Id("F"))))))));

    private static Formula SequenceDefinition()
    {
        var r = F.Id("r");
        return Disp(new Formula.Aligned([
            Equal(Call("P", D(0)), D(1)),
            Seq(Bound("r", Naturals()), Equal(Call("P", Add(r, D(1))), Step(Call("P", r)))),
            Seq(Bound("n", Naturals()), Equal(Call("a", N()),
                Coefficient(N(), Call("P", Add(N(), D(1))))))
        ]));
    }

    private static Formula UniqueFormula() => Disp(Seq(Bound("B", Series()),
        Implication(Equal(Constant(F.Id("B")), D(1)),
            Implication(Equation(F.Id("B")), Equal(F.Id("B"), A())))));

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(0), Sp, Lt, Sp, N()),
            Parenthesized(Seq(Call("Odd", Call("a", N())), Sp, Iff, Sp,
                Parenthesized(Seq(Exists, Sp, F.Id("k"), Colon, Sp, Naturals(), Comma, Sp,
                    Equal(N(), Power(D(2), F.Id("k"))))))))));
}
