using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class ThetaSelfCompositionModFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/ThetaSelfCompositionModFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2025a378581");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive coefficients of OEIS A378581 are two modulo four exactly at square degrees.",
        H("Theta Self-Composition Modulo Four"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's entry hanna2025a378581 defines the integer "
                + "series A by A(x*A(x))=theta_3(x), where theta_3(x) is one plus twice "
                + "the sum of x^(j^2) over positive integers j. It conjectures that "
                + "positive square degrees have coefficient two modulo four and all "
                + "other positive degrees have coefficient divisible by four.")),
            Paragraph(Text("All indices are natural numbers. PowerSeries(Z) is the ring "
                + "of integer formal power series, X is its indeterminate, coeff(n,F) "
                + "extracts a coefficient, and mk constructs a series from its coefficient "
                + "function. In the formulas subst(F,U) means F(U), with the outer series "
                + "first. IsSquare(n) means that n is the square of a natural number. "
                + "The map operation applies its ring homomorphism to every coefficient; "
                + "all remainders in the final formula are integer remainders.")),
            Node("thetaSeries", "The formal theta series", ThetaFormula(),
                "The coefficient function includes the constant term separately from "
                + "the positive square degrees.", DescribeRole.Definition),
            Node("coeff_thetaSeries", "The theta coefficients", ThetaCoefficientFormula(),
                "Extracting a coefficient from mk gives the defining conditional expression."),
            Node("a", "The stabilized integer coefficients", SequenceFormula(),
                "The auxiliary approximation starts at one and applies the displayed "
                + "correction. Each approximation has constant coefficient one. Agreement "
                + "below degree d improves to agreement below degree d+1, so the diagonal "
                + "coefficient defines the sequence.", DescribeRole.Definition),
            Node("generatingSeries", "The integer generating series",
                Disp(Equal(A(), Call("mk", Named("a")))),
                "The generating series has coefficient function a.", DescribeRole.Definition),
            Node("generating_equation", "The defining functional equation", EquationFormula(),
                "If F and G agree below degree d and G has constant coefficient one, "
                + "then at every degree n at most d the difference between F(X*F) and "
                + "G(X*G) equals the difference between their degree-n coefficients. "
                + "The substitution arguments agree through degree d. In the remaining "
                + "outer difference, lower terms vanish and the degree-n term has "
                + "multiplier one. The correction therefore contracts coefficient "
                + "agreement. Its stabilized series is a fixed point, giving the equation."),
            Node("generating_unique", "Uniqueness of the integer solution", UniqueFormula(),
                "Every solution is a fixed point of the correction. Induction on degree "
                + "using the same contraction proves equality of all coefficients."),
            Node("mod_four_identity", "The full series identity modulo four", ModFourFormula(),
                "Write the reduced theta series as R=1+2*S. In ZMod(4), twice X*R "
                + "equals twice X. More generally, c*U=c*V implies c*U^k=c*V^k by "
                + "induction on k, and the coefficient formula for substitution then "
                + "gives c*F(U)=c*F(V) for zero-constant U and V. Apply this with c=2 "
                + "to obtain R(X*R)=R. Mapping the integer equation preserves "
                + "substitution, and uniqueness over ZMod(4) identifies the two series."),
            Node("hanna_conjecture", "Hanna's A378581 conjecture", ConjectureFormula(),
                "At positive degree, the theta coefficient is two at a square and "
                + "zero otherwise. The series identity and the integer-cast remainder "
                + "equivalence give both biconditionals, as conjectured in hanna2025a378581.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a378581-theta-self-composition-mod-four"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a378581-" + name.Replace('_', '-').ToLowerInvariant()),
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
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) => Seq(
        Named("if"), Sp, Parenthesized(condition), Sp, Named("then"), Sp, yes, Sp,
        Named("else"), Sp, no);
    private static Formula ThetaCoefficient(Formula n) =>
        IfThenElse(Equal(n, D(0)), D(1),
            Parenthesized(IfThenElse(Call("IsSquare", n), D(2), D(0))));
    private static Formula Compose(Formula series) => Call("subst", series, Mul(X(), series));
    private static Formula Equation(Formula series) => Equal(Compose(series), Theta());
    private static Formula Approx(Formula depth) => Call("approximation", depth);
    private static Formula ModFour(Formula series) =>
        Call("map", Call("intCastRingHom", Call("ZMod", D(4))), series);

    private static Formula ThetaFormula() => Disp(Equal(Theta(), Call("mk",
        Parenthesized(Seq(N(), Colon, Sp, Naturals(), Sp, Mapsto, Sp, ThetaCoefficient(N()))))));

    private static Formula ThetaCoefficientFormula() => Disp(Seq(Bound("n", Naturals()),
        Equal(Call("coeff", N(), Theta()), ThetaCoefficient(N()))));

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
