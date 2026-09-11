using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class QuadraticSquareReversionDyadicSupportParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/QuadraticSquareReversionDyadicSupportParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2025a380678");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's A380678 series has odd coefficients exactly at the indices of A027383.",
        H("Square-Denominator Reversion and Dyadic Support"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's entry hanna2025a380678 specifies "
                + "A(x-A(x)^2/(1-A(x)^2))=x. Its conjecture says that, for n at least "
                + "one, a(n) is odd exactly when n=3*2^m-2 or n=4*2^m-2 for a "
                + "natural m. The equivalent formulas below use n+2, since the "
                + "two products are at least three and four respectively.")),
            Paragraph(Text("A denotes generatingSeries and T denotes its private "
                + "approximations, all over the integers. X is the indeterminate. "
                + "The operator coeff(n,f) extracts a coefficient, mk constructs a "
                + "series from its coefficient function, and subst(f,g) composes f "
                + "with g. The operation invOfUnit(f,1) is the formal power-series "
                + "inverse with prescribed constant unit one; every denominator "
                + "used here has constant coefficient one. All indices and exponents "
                + "are natural numbers.")),
            Paragraph(Text("P denotes the imported lacunarySeries from "
                + "D5.S1.Recurrence.Invariants.QuadraticReversionDyadicSupportParity. "
                + "It has coefficients in ZMod(2), with coefficient one exactly when "
                + "n+2=3*2^m or n+2=4*2^m for some natural m, and zero otherwise. "
                + "The operator map applies its ring homomorphism coefficientwise; "
                + "intCastRingHom(ZMod(2)) is the canonical map from the integers.")),
            Node("generatingSeries", "The integral generating series", GeneratingFormula(),
                "For zero-constant f and g, clearing the unit denominators factors "
                + "the difference of f^2/(1-f^2) and g^2/(1-g^2) as "
                + "(f-g)(f+g) times the two inverses. The factor f+g has zero "
                + "constant coefficient, so the inner arguments gain one degree "
                + "of agreement. Substitution by an argument with linear coefficient "
                + "one preserves the first coefficient of a difference. Thus the "
                + "displayed transformation gains one degree of agreement, and "
                + "its diagonal coefficient limit is well defined.", DescribeRole.Definition),
            Node("a", "The coefficient sequence", CoefficientFormula(),
                "The integer a(n) is the coefficient of degree n in A.", DescribeRole.Definition),
            Node("generating_equation", "The OEIS equation and normalization", EquationFormula(),
                "The coefficient limit is fixed by f+X-subst(f,X-f^2/(1-f^2)). "
                + "Rearranging gives exactly the functional equation in "
                + "hanna2025a380678. The approximations have zero constant "
                + "coefficient, and their stable linear coefficient is one."),
            Node("generating_unique", "Uniqueness of the normalized solution", UniqueFormula(),
                "Every zero-constant solution is fixed by the same transformation. "
                + "Induction on the degree of agreement proves equality with A. "
                + "In particular, this applies under both displayed normalization hypotheses."),
            Node("mod_two_identity", "Reduction to the imported support series",
                Disp(Equal(Reduced(), P())),
                "Mapping the integral equation commutes with substitution and "
                + "the inverse of its unit denominator. In characteristic two, "
                + "1-f^2=(1-f)^2. Cancellation of this unit shows that its inverse "
                + "is invOfUnit(1-f,1)^2. Therefore the imported lacunary_reversion "
                + "identity for P is also the square-denominator equation. The "
                + "imported lacunary_quadratic identity gives constant coefficient "
                + "zero. Applying the same degree-contraction uniqueness argument "
                + "over ZMod(2) identifies the reduction of A with P."),
            Node("hanna_conjecture", "Hanna's parity conjecture", ConjectureFormula(),
                "Extracting coefficient n from the reduction identity gives the "
                + "indicator of the two dyadic families. Mathlib's "
                + "intCast_eq_one_iff_odd identifies an integer's image being one "
                + "in ZMod(2) with its being odd.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a380678-quadratic-square-reversion-dyadic-support-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a380678-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula A() => F.Id("A");
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
        Subtract(X(), Mul(Power(f, D(2)),
            Call("invOfUnit", Subtract(D(1), Power(f, D(2))), D(1))));
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

    private static Formula Equation(Formula f) => Equal(Call("subst", f, Inner(f)), X());

    private static Formula EquationFormula() => Disp(And(
        Equal(Call("constantCoeff", A()), D(0)), And(
            Equal(Call("coeff", D(1), A()), D(1)), Equation(A()))));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("B", Call("PowerSeries", Integers())),
            Implication(Equal(Call("constantCoeff", b), D(0)),
                Implication(Equal(Call("coeff", D(1), b), D(1)),
                    Implication(Equation(b), Equal(b, A()))))));
    }

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Le, Sp, N()),
            Parenthesized(Seq(Call("Odd", Call("a", N())), Sp, Iff, Sp,
                Parenthesized(Support(N())))))));
}
