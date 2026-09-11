using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class QuadraticSquareReversionModFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/QuadraticSquareReversionModFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2025a389542");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of OEIS A389542 satisfy Hanna's mod-four classification.",
        H("Quadratic Square Reversion Modulo Four"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2025a389542 defines A by "
                + "A(A(x)^2-x^2)=4A(x)^3. For n greater than one, its conjecture "
                + "asserts that a(n) is congruent to two modulo four at indices "
                + "one more than a power of two, and divisible by four elsewhere.")),
            Paragraph(Text("All indices are natural numbers and all coefficients are "
                + "integers. R denotes inverseSeries, A denotes generatingSeries, and X "
                + "is the indeterminate. The local series P(n) are the approximations "
                + "and H is their coefficientwise limit. The operator mk constructs a "
                + "series from its coefficient function; coeff(n,B) extracts its nth "
                + "coefficient; subst(B,C) substitutes C into B; inv(R) denotes "
                + "Mathlib's substInvOfIsUnit with the proved unit linear coefficient. "
                + "K denotes catalanSeries from CatalanCompositionSquareParity, the "
                + "integer series with zero constant coefficient satisfying K=X+K^2. "
                + "The map pi sends integers to ZMod(4), and map(pi,B) applies pi "
                + "coefficientwise. The operator mod denotes integer remainder.")),
            Node("inverseSeries", "The integral inverse", InverseFormula(),
                "The map defining P preserves zero constant coefficient and increases "
                + "coefficient agreement by one degree. Thus the displayed diagonal "
                + "limit H satisfies H=-X-H^2-2XH(4X^3). The series R=X(1+2H) "
                + "has zero constant coefficient and linear coefficient one.",
                DescribeRole.Definition),
            Node("generatingSeries", "The generating series",
                Disp(Equal(A(), Call("inv", R()))),
                "The compositional inverse is defined over the integers and satisfies "
                + "R(A)=X and A(R)=X.", DescribeRole.Definition),
            Node("a", "The coefficient sequence", CoefficientFormula(),
                "The integer a(n) is the coefficient of degree n in A.", DescribeRole.Definition),
            Node("inverse_equation", "The quadratic inverse equation",
                Disp(Equal(Power(R(), D(2)), Subtract(Power(X(), D(2)),
                    Call("subst", R(), Mul(D(4), Power(X(), D(3))))))),
                "Expanding R=X(1+2H), its defining correction equation gives "
                + "R^2=X^2-R(4X^3) exactly over the integers."),
            Node("generating_equation", "The OEIS equation and normalization", EquationFormula(),
                "Substituting A into the inverse equation gives "
                + "R(4A^3)=A^2-X^2. Composing with A gives the stated functional "
                + "equation. Integral compositional inversion gives the two "
                + "normalization conditions."),
            Node("generating_unique", "Uniqueness of the normalized solution", UniqueFormula(),
                "A normalized solution B has an integral compositional inverse S. "
                + "Transporting its equation gives S^2=X^2-S(4X^3). To compare "
                + "S with R, pass injectively to rational coefficients and write "
                + "S=Xu and R=Xv. Both units satisfy u^2=1-4Xu(4X^3), and their "
                + "sum has constant coefficient two. Multiplying the difference by "
                + "this unit and using substitution increases coefficient agreement "
                + "by one degree. Induction gives S=R and hence B=A."),
            Node("mod_four_identity", "The Catalan correction modulo four",
                Disp(Equal(Reduce(A()), Add(X(), Mul(Mul(D(2), X()), Reduce(K()))))),
                "Reducing the correction equation modulo two gives H=X+H^2. "
                + "The factor 1-H-K is a unit, so comparison with K=X+K^2 yields "
                + "H=K modulo two. Also R=X modulo two, whence A=X modulo two. "
                + "Therefore AH(A)=XK modulo two. Doubling lifts this equality "
                + "modulo four; R(A)=A+2AH(A)=X then gives A=X+2XK modulo four."),
            Node("hanna_conjecture", "Hanna's coefficient conjecture", HannaFormula(),
                "The frozen binary_catalan theorem states that the coefficient of "
                + "degree m in K is odd exactly when m is a power of two. For "
                + "n greater than one, the mod-four identity gives a(n)=2 coeff(n-1,K) "
                + "modulo four. An odd coefficient gives remainder two and an even "
                + "coefficient gives remainder zero, proving both biconditionals.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a389542-quadratic-square-reversion-mod-four"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a389542-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula X() => F.Id("X");
    private static Formula R() => F.Id("R");
    private static Formula A() => F.Id("A");
    private static Formula K() => F.Id("K");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula Conjunction(Formula first, Formula second) =>
        Seq(Parenthesized(first), Sp, Land, Sp, Parenthesized(second));
    private static Formula Reduce(Formula series) => Call("map", F.Id("pi"), series);
    private static Formula Equation(Formula series) => Equal(
        Call("subst", series, Parenthesized(Subtract(Power(series, D(2)), Power(X(), D(2))))),
        Mul(D(4), Power(series, D(3))));

    private static Formula InverseFormula()
    {
        Formula n = F.Id("n");
        Formula h = F.Id("H");
        Formula p = Call("P", n);
        Formula next = Subtract(Subtract(Seq(Minus, X()), Power(p, D(2))),
            Mul(Mul(D(2), X()), Call("subst", p, Mul(D(4), Power(X(), D(3))))));
        return Disp(new Formula.Aligned([
            Equal(Call("P", D(0)), D(0)),
            Seq(Bound("n", Naturals()), Equal(Call("P", Add(n, D(1))), next)),
            Equal(h, Call("mk", Parenthesized(Seq(n, Sp, Mapsto, Sp,
                Call("coeff", n, Call("P", Add(n, D(1)))))))),
            Equal(R(), Mul(X(), Parenthesized(Add(D(1), Mul(D(2), h)))))
        ]));
    }

    private static Formula CoefficientFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Bound("n", Naturals()), Equal(Call("a", n), Call("coeff", n, A()))));
    }

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

    private static Formula HannaFormula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula support = Seq(Exists, Sp, k, Colon, Sp, Naturals(), Comma, Sp,
            Equal(n, Add(Power(D(2), k), D(1))));
        Formula remainder = new Formula.Modulo(Call("a", n), D(4));
        Formula two = Seq(Equal(remainder, D(2)), Sp, Iff, Sp, Parenthesized(support));
        Formula zero = Seq(Equal(remainder, D(0)), Sp, Iff, Sp, Neg, Sp, Parenthesized(support));
        return Disp(Seq(Bound("n", Naturals()),
            Implication(Seq(D(1), Sp, Lt, Sp, n), Parenthesized(Conjunction(two, zero)))));
    }
}
