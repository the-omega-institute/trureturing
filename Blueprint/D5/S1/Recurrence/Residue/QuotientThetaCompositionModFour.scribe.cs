using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class QuotientThetaCompositionModFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/QuotientThetaCompositionModFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2025a378580");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive coefficients of OEIS A378580 are two modulo four exactly at square degrees.",
        H("Quotient Theta Composition Modulo Four"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's entry hanna2025a378580 defines the integer "
                + "series A by A(x/A(x))=theta_3(x), where theta_3(x) is one plus twice "
                + "the sum of x^(j^2) over positive integers j. It conjectures that "
                + "positive square degrees have coefficient two modulo four and all "
                + "other positive degrees have coefficient divisible by four.")),
            Paragraph(Text("All indices are natural numbers. PowerSeries(Z) is the ring "
                + "of integer formal power series, X is its indeterminate, coeff(n,F) "
                + "extracts a coefficient, and mk constructs a series from its coefficient "
                + "function. In the formulas subst(F,U) means F(U), with the outer series "
                + "first. IsSquare(n) means that n is the square of a natural number. "
                + "The map operation applies its ring homomorphism to every coefficient; "
                + "all remainders in the final formula are integer remainders. The notation "
                + "invOfUnit(F,1) denotes the formal multiplicative inverse when F has "
                + "constant coefficient one. The imported thetaSeries is "
                + "D5.S1.Recurrence.Parity.ThetaSelfCompositionModFour.thetaSeries: its "
                + "degree-zero coefficient is one, its positive square coefficients are "
                + "two, and all other coefficients are zero.")),
            Node("inverse_agreement", "Inverse agreement below a degree", InverseAgreementFormula(),
                "If X^d divides G-F, it divides invOfUnit(F,1)*(G-F)*invOfUnit(G,1). "
                + "The inverse identities identify that product with the difference of "
                + "the two inverses. Thus their coefficients agree below d."),
            Node("quotient_triangular", "The triangular quotient comparison", TriangularFormula(),
                "Inverse agreement makes X*invOfUnit(F,1) and X*invOfUnit(G,1) agree "
                + "below d+1. Their powers therefore agree there too. In the coefficient "
                + "sum for the remaining outer difference, terms below n cancel, terms "
                + "above n vanish, and the degree-n multiplier is one."),
            Node("a", "The stabilized integer coefficients", SequenceFormula(),
                "The auxiliary approximation starts at one and applies the displayed "
                + "correction. Each approximation has constant coefficient one. Agreement "
                + "below degree d improves to agreement below degree d+1, so the diagonal "
                + "coefficient defines the sequence.", DescribeRole.Definition),
            Node("generatingSeries", "The integer generating series",
                Disp(Equal(A(), Call("mk", Named("a")))),
                "The generating series has coefficient function a.", DescribeRole.Definition),
            Node("generating_equation", "The defining functional equation", EquationFormula(),
                "The quotient triangular comparison shows that the correction improves "
                + "agreement below d to agreement below d+1. The diagonal coefficients "
                + "therefore stabilize. The resulting series is a fixed point of the "
                + "correction, which yields exactly the quotient functional equation."),
            Node("generating_unique", "Uniqueness of the integer solution", UniqueFormula(),
                "Every solution is a fixed point of the correction. Induction on degree "
                + "using the same contraction proves equality of all coefficients."),
            Node("mod_four_identity", "The full series identity modulo four", ModFourFormula(),
                "Write the reduced theta series as T=1+2*S. Since 4=0 in ZMod(4), "
                + "T*T=1, so invOfUnit(T,1)=T. The imported product generating equation "
                + "and its modulo-four identity give subst(T,X*T)=T; consequently T "
                + "also satisfies the quotient equation. Mapping the integer quotient "
                + "equation preserves both substitution and unit inversion. Quotient "
                + "uniqueness over ZMod(4) identifies its solution with T."),
            Node("hanna_conjecture", "Hanna's A378580 conjecture", ConjectureFormula(),
                "At positive degree, the theta coefficient is two at a square and "
                + "zero otherwise. The series identity and the integer-cast remainder "
                + "equivalence give both biconditionals, as conjectured in hanna2025a378580.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a378580-quotient-theta-composition-mod-four"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a378580-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula X() => F.Id("X");
    private static Formula N() => F.Id("n");
    private static Formula A() => Named("generatingSeries");
    private static Formula Theta() => Named("thetaSeries");
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
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Biconditional(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Iff, Sp, Parenthesized(right));
    private static Formula Inverse(Formula series) => Call("invOfUnit", series, D(1));
    private static Formula Compose(Formula series) => Call("subst", series, Mul(X(), Inverse(series)));
    private static Formula Equation(Formula series) => Equal(Compose(series), Theta());
    private static Formula Approx(Formula depth) => Call("approximation", depth);
    private static Formula ModFour(Formula series) =>
        Call("map", Call("intCastRingHom", Call("ZMod", D(4))), series);

    private static Formula Agreement(Formula left, Formula right) => Seq(Bound("k", Naturals()),
        Implication(Seq(F.Id("k"), Sp, Lt, Sp, F.Id("d")),
            Equal(Call("coeff", F.Id("k"), left), Call("coeff", F.Id("k"), right))));

    private static Formula GeneralComparison(Formula conclusion)
    {
        Formula r = F.Id("R");
        Formula f = F.Id("f");
        Formula g = F.Id("g");
        return Disp(Seq(Bound("R", Named("Type")),
            Implication(Call("CommRing", r), Seq(Bound("d", Naturals()),
                Bound("f", Call("PowerSeries", r)), Bound("g", Call("PowerSeries", r)),
                Implication(Equal(Call("constantCoeff", f), D(1)),
                    Implication(Equal(Call("constantCoeff", g), D(1)),
                        Implication(Agreement(f, g), conclusion)))))));
    }

    private static Formula InverseAgreementFormula() => GeneralComparison(Seq(Bound("n", Naturals()),
        Implication(Seq(N(), Sp, Lt, Sp, F.Id("d")),
            Equal(Call("coeff", N(), Inverse(F.Id("f"))),
                Call("coeff", N(), Inverse(F.Id("g")))))));

    private static Formula TriangularFormula()
    {
        Formula f = F.Id("f");
        Formula g = F.Id("g");
        return GeneralComparison(Seq(Bound("n", Naturals()),
            Implication(Seq(N(), Sp, Le, Sp, F.Id("d")),
                Equal(Subtract(Call("coeff", N(), Compose(f)), Call("coeff", N(), Compose(g))),
                    Subtract(Call("coeff", N(), f), Call("coeff", N(), g))))));
    }

    private static Formula SequenceFormula()
    {
        Formula d = F.Id("d");
        return Disp(new Formula.Aligned([
            Seq(Bound("n", Naturals()), Equal(Call("a", N()),
                Call("coeff", N(), Approx(Add(N(), D(1)))))),
            Equal(Approx(D(0)), D(1)),
            Seq(Bound("d", Naturals()), Equal(Approx(Add(d, D(1))),
                Subtract(Parenthesized(Add(Theta(), Approx(d))), Compose(Approx(d)))))
        ]));
    }

    private static Formula EquationFormula() => Disp(Conjunction(
        Equal(Call("constantCoeff", A()), D(1)), Equation(A())));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Series()),
            Implication(Equal(Call("constantCoeff", b), D(1)),
                Implication(Equation(b), Equal(b, A())))));
    }

    private static Formula ModFourFormula() => Disp(Equal(ModFour(A()), ModFour(Theta())));

    private static Formula ConjectureFormula()
    {
        Formula remainder = new Formula.Modulo(Call("a", N()), D(4));
        Formula square = Call("IsSquare", N());
        return Disp(Seq(Bound("n", Naturals()),
            Implication(Seq(D(0), Sp, Lt, Sp, N()), Parenthesized(Conjunction(
                Biconditional(Equal(remainder, D(2)), square),
                Biconditional(Equal(remainder, D(0)), Seq(Neg, Sp, Parenthesized(square))))))));
    }
}
