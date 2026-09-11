using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class QuadraticReversionDyadicSupportParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/QuadraticReversionDyadicSupportParity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's A389476 series has odd coefficients exactly at the indices of A027383.",
        H("Quadratic Reversion and Dyadic Support"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's OEIS entry hanna2025a389476 defines "
                + "A(x-A(x)^2/(1-A(x))^2)=x and conjectures that a(n) is odd precisely "
                + "at indices 3*2^m-2 or 4*2^m-2 for natural m. The formulas below use "
                + "n+2=3*2^m or n+2=4*2^m. The products are at least three and four, "
                + "so this is equivalent to the natural-subtraction formulation.")),
            Paragraph(Text("A denotes generatingSeries, U denotes innerSeries, and P "
                + "denotes lacunarySeries. The first two series and the approximation T "
                + "have integer coefficients; P has coefficients in ZMod(2). X is the "
                + "indeterminate in the indicated coefficient ring. PowerSeries(R) denotes "
                + "formal power series over R, coeff(n,f) extracts a coefficient, and mk "
                + "constructs a series from its coefficient function. The notation subst(f,g) "
                + "means f composed with g. The operation invOfUnit(f,1) is Mathlib's "
                + "power-series inverse with prescribed constant unit one. Every denominator "
                + "here has constant coefficient one. All indices and exponents are natural numbers.")),
            Node("generatingSeries", "The integer series", GeneratingFormula(),
                "Starting from zero, the transformation f+X-subst(f,u(f)), where "
                + "u(f)=X-(f*invOfUnit(1-f,1))^2, preserves zero constant coefficient. "
                + "If two zero-constant inputs agree below degree d, their inner arguments agree below "
                + "degree d+1. Substitution by an argument with linear coefficient one "
                + "preserves the first coefficient of a difference. The transformation "
                + "therefore gains one degree of agreement, making the displayed "
                + "coefficientwise construction stable.", DescribeRole.Definition),
            Node("a", "The coefficient sequence", CoefficientFormula(),
                "The integer sequence consists of the coefficients of A.", DescribeRole.Definition),
            Node("innerSeries", "The inner argument", Disp(Equal(U(), Inner(A()))),
                "The square of the product of A and the prescribed inverse gives A^2/(1-A)^2 "
                + "in the ring of formal power series.", DescribeRole.Definition),
            Node("generating_equation", "The generating equation and normalization", EquationFormula(),
                "Stabilization gives the reversion equation and constant coefficient zero. "
                + "The linear coefficient is one. Multiplication by the square of the "
                + "unit denominator gives the last conjunct, identifying U with the "
                + "rational expression in Hanna's equation."),
            Node("generating_unique", "Uniqueness of integer reversion", UniqueFormula(),
                "Every zero-constant solution is fixed by the same transformation. "
                + "Induction on the degree of agreement proves equality with A. "
                + "A separate linear-coefficient hypothesis is unnecessary."),
            Node("lacunarySeries", "The dyadic support series", LacunaryFormula(),
                "The coefficient is the indicator of the union of the two dyadic "
                + "families, with values zero and one in ZMod(2).", DescribeRole.Definition),
            Node("lacunary_quadratic", "The quadratic identity", Disp(Equal(P(),
                Add(Add(X(), Power(X(), D(2))), Mul(Power(X(), D(2)), Power(P(), D(2)))))),
                "The support contains 1 and 2 and excludes 0. Beyond these indices, "
                + "n+2 lies in the support exactly when n is even and n/2 lies in the "
                + "support. Factoring a power of two from the defining equalities proves "
                + "this equivalence. Frobenius identifies P^2 with subst(P,X^2), and "
                + "coefficient extraction gives the quadratic identity."),
            Node("lacunary_reversion", "Reversion in characteristic two",
                Disp(Equal(Call("subst", P(), Inner(P())), X())),
                "Put z=P, v=invOfUnit(1-P,1), and r=X+(z*v)^2. Clearing the unit "
                + "denominator in the quadratic identity gives (1+X)*r=z*v. Squaring "
                + "gives r+X=(1+X^2)*r^2 and hence X=r+r^2+r^2*X^2. Composing "
                + "the quadratic identity with r gives the same equation for subst(P,r). "
                + "The factor r^2 increases the degree of agreement, so induction proves "
                + "uniqueness and subst(P,r)=X. In characteristic two, r is Inner(P)."),
            Node("mod_two_identity", "Reduction equals the support series", Disp(Equal(Reduced(), P())),
                "Map the proved integer generating equation through the canonical "
                + "homomorphism to ZMod(2). A unit-denominator cancellation shows that "
                + "mapping commutes with the inner argument, and Mathlib's map_subst "
                + "transports composition. The generic reversion uniqueness proof then "
                + "identifies the reduced series with P."),
            Node("hanna_conjecture", "Hanna's parity conjecture", ConjectureFormula(),
                "Extract coefficient n from the reduction identity. The coefficient of P "
                + "is one exactly on its defining dyadic support, and an integer maps "
                + "to one in ZMod(2) exactly when it is odd.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Arith/hanna2025a389476")),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a389476-quadratic-reversion-dyadic-support-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("quadratic-reversion-dyadic-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula A() => F.Id("A");
    private static Formula U() => F.Id("U");
    private static Formula P() => F.Id("P");
    private static Formula X() => F.Id("X");
    private static Formula N() => F.Id("n");
    private static Formula M() => F.Id("m");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) => Seq(left, Sp, Plus, Sp, right);
    private static Formula Subtract(Formula left, Formula right) =>
        Seq(left, Sp, Minus, Sp, Parenthesized(right));
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
    private static Formula Function(string name, Formula body) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, Naturals(), Sp, Mapsto, Sp, body));
    private static Formula Inner(Formula f) =>
        Subtract(X(), Power(Mul(f, Call("invOfUnit", Subtract(D(1), f), D(1))), D(2)));
    private static Formula T(Formula n) => Call("T", n);
    private static Formula Reduced() => Call("map", Call("intCastRingHom", Call("ZMod", D(2))), A());

    private static Formula Support(Formula n) => Seq(Exists, Sp, M(), Colon, Sp, Naturals(), Comma, Sp,
        Parenthesized(Seq(
            Equal(Add(n, D(2)), Mul(D(3), Power(D(2), M()))), Sp, Lor, Sp,
            Equal(Add(n, D(2)), Mul(D(4), Power(D(2), M()))))));

    private static Formula GeneratingFormula() => Disp(new Formula.Aligned([
        Equal(T(D(0)), D(0)),
        Seq(Bound("n", Naturals()), Equal(T(Add(N(), D(1))),
            Subtract(Add(T(N()), X()), Call("subst", T(N()), Inner(T(N())))))),
        Equal(A(), Call("mk", Function("n", Call("coeff", N(), T(Add(N(), D(1)))))))
    ]));

    private static Formula CoefficientFormula() => Disp(Seq(Bound("n", Naturals()),
        Equal(Call("a", N()), Call("coeff", N(), A()))));

    private static Formula EquationFormula() => Disp(And(
        Equal(Call("constantCoeff", A()), D(0)), And(
            Equal(Call("coeff", D(1), A()), D(1)), And(
                Equal(Call("subst", A(), U()), X()),
                Equal(Mul(Power(Subtract(D(1), A()), D(2)), Subtract(X(), U())),
                    Power(A(), D(2)))))));

    private static Formula UniqueFormula()
    {
        Formula f = F.Id("f");
        return Disp(Seq(Bound("f", Call("PowerSeries", Integers())),
            Implication(Equal(Call("constantCoeff", f), D(0)),
                Implication(Equal(Call("subst", f, Inner(f)), X()), Equal(f, A())))));
    }

    private static Formula LacunaryFormula() => Disp(Equal(P(), Call("mk", Function("n",
        Seq(Named("if"), Sp, Parenthesized(Support(N())), Sp, Named("then"), Sp, D(1), Sp,
            Named("else"), Sp, D(0))))));

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Le, Sp, N()),
            Parenthesized(Seq(Call("Odd", Call("a", N())), Sp, Iff, Sp,
                Parenthesized(Support(N())))))));
}
