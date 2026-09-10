using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class UnitReversionSquareParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/UnitReversionSquareParity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized integer solution of Hanna's A373312 equation has odd coefficients exactly at positive Mersenne indices.",
        H("Unit Reversion and Square Parity"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's OEIS entry hanna2024a373312 specifies "
                + "A(x)^2=A(x*A(x)/(1-A(x))^2) and conjectures that a(n) is odd exactly "
                + "when n=2^k-1 for k at least one. The normalization is A(0)=0 and a(1)=1.")),
            Paragraph(Text("Here A denotes generatingSeries and U denotes innerSeries. "
                + "PowerSeries(R) denotes formal power series over R, X is the indeterminate, "
                + "coeff(n,f) extracts coefficient n, and mk builds a series from a coefficient "
                + "function. The notation subst(f,g) means f composed with g. The operation "
                + "invOfUnit(f,1) is the power-series inverse with prescribed constant unit 1; "
                + "every denominator used below has constant coefficient 1. The auxiliary "
                + "P(n), r(f), and q(f) in the construction are integer power series. Indices "
                + "and exponents are natural numbers, including subtraction in 2^k-1; a(n) "
                + "is an integer. In the mod-two identity X and the arithmetic lie over ZMod(2).")),
            Node("generatingSeries", "Construction of the integer series", GeneratingFormula(),
                "Write A=X*B. The equation B=r(B)^2*subst(B,q(B)) contracts agreement "
                + "by one degree for series of constant coefficient 1. The inverse r(B) "
                + "gains a degree of agreement, while q(B) has order at least two, so "
                + "outer substitution doubles the degree of agreement. Consequently "
                + "coefficient n of P(n) has stabilized, and these coefficients define B.",
                DescribeRole.Definition),
            Node("a", "The integer coefficient sequence", CoefficientFormula(),
                "The sequence is defined by coefficient extraction from A.",
                DescribeRole.Definition),
            Node("innerSeries", "The unit-denominator argument", InnerFormula(),
                "Since A has zero constant coefficient, 1-A is a unit. Mathlib's "
                + "invOfUnit_mul identifies the prescribed inverse with the denominator "
                + "in Hanna's functional equation.", DescribeRole.Definition),
            Node("generating_equation", "The normalized generating equation", EquationFormula(),
                "Stabilization gives B=r(B)^2*subst(B,q(B)). Multiplication by X^2*B "
                + "and the substitution multiplication law give A^2=subst(A,U). The "
                + "initial constant coefficient of B is 1, giving both normalization identities."),
            Node("generating_unique", "Uniqueness over the integers", UniqueFormula(),
                "The zero constant coefficient gives f=X*B, and the linear coefficient "
                + "gives B(0)=1. Cancellation of the nonzero factor X^2*B turns the "
                + "functional equation into the same contracting fixed-point equation. "
                + "Induction on the degree of agreement identifies B with the constructed series."),
            Node("mod_two_fixed", "The lacunary fixed-point equation", ModTwoFormula(),
                "Map the proved generating equation to ZMod(2). Frobenius identifies "
                + "A^2 with subst(A,X^2). Mathlib's compositional inverse cancels the "
                + "outer series A, whose linear coefficient is 1, and gives U=X^2. "
                + "Clearing the unit denominator and cancelling X yields A=X*(1-A)^2. "
                + "Characteristic two and Frobenius give the displayed equation."),
            Node("hanna_conjecture", "Hanna's parity conjecture", ConjectureFormula(),
                "The fixed-point equation gives coefficient 1 equal to 1. For n positive, "
                + "coefficient n+1 is zero when n is odd, and is coefficient n/2 when n "
                + "is even. The index n+1 is a positive Mersenne index exactly when "
                + "n is even and n/2 is a positive Mersenne index. Strong induction, "
                + "with constant coefficient zero, proves the support classification. "
                + "An integer maps to 1 in ZMod(2) exactly when it is odd.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Arith/hanna2024a373312")),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a373312-unit-reversion-square-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("unit-reversion-square-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula A() => F.Id("A");
    private static Formula U() => F.Id("U");
    private static Formula X() => F.Id("X");
    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
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
    private static Formula P(Formula index) => Call("P", index);
    private static Formula Reciprocal(Formula series) =>
        Call("invOfUnit", Subtract(D(1), series), D(1));
    private static Formula Inner(Formula series) =>
        Mul(Mul(X(), series), Power(Reciprocal(series), D(2)));
    private static Formula Reduced() => Call("map", Call("intCastRingHom", Call("ZMod", D(2))), A());

    private static Formula GeneratingFormula()
    {
        Formula f = F.Id("f");
        return Disp(new Formula.Aligned([
            Seq(Bound("f", Call("PowerSeries", Integers())),
                Equal(Call("r", f), Reciprocal(Mul(X(), f)))),
            Seq(Bound("f", Call("PowerSeries", Integers())),
                Equal(Call("q", f), Mul(Mul(Power(X(), D(2)), f), Power(Call("r", f), D(2))))),
            Equal(P(D(0)), D(1)),
            Seq(Bound("n", Naturals()), Equal(P(Add(N(), D(1))),
                Mul(Power(Call("r", P(N())), D(2)), Call("subst", P(N()), Call("q", P(N())))))),
            Equal(A(), Mul(X(), Call("mk", Function("n", Call("coeff", N(), P(N()))))))
        ]));
    }

    private static Formula CoefficientFormula() => Disp(Seq(Bound("n", Naturals()),
        Equal(Call("a", N()), Call("coeff", N(), A()))));

    private static Formula InnerFormula() => Disp(Equal(U(), Inner(A())));

    private static Formula EquationFormula() => Disp(And(
        Equal(Call("constantCoeff", A()), D(0)), And(
            Equal(Call("coeff", D(1), A()), D(1)),
            Equal(Power(A(), D(2)), Call("subst", A(), U())))));

    private static Formula UniqueFormula()
    {
        Formula f = F.Id("f");
        return Disp(Seq(Bound("f", Call("PowerSeries", Integers())),
            Implication(Equal(Call("constantCoeff", f), D(0)),
                Implication(Equal(Call("coeff", D(1), f), D(1)),
                    Implication(Equal(Power(f, D(2)), Call("subst", f, Inner(f))),
                        Equal(f, A()))))));
    }

    private static Formula ModTwoFormula() => Disp(Equal(Reduced(),
        Add(X(), Mul(X(), Call("subst", Reduced(), Power(X(), D(2)))))));

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Positive(N()), Parenthesized(Seq(Call("Odd", Call("a", N())), Sp, Iff, Sp,
            Seq(Exists, Sp, K(), Colon, Sp, Naturals(), Comma, Sp,
                And(Positive(K()), Equal(N(), Subtract(Power(D(2), K()), D(1))))))))));
}
