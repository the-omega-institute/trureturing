using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CatalanCompositionSquareParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2024a374570");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized solution of OEIS A374570 has odd coefficients above degree one exactly at powers of two plus one.",
        H("Catalan Composition and Hanna's Parity Conjecture"),
        Blocks(
            Paragraph(Text("The generating equation and parity conjecture are recorded "
                + "in hanna2024a374570. Write C for catalanSeries and A for generatingSeries. "
                + "All coefficient indices and exponents are natural numbers. The series "
                + "A, C, D, and B(r) have integer coefficients; X is the indeterminate. "
                + "The operator subst(f,u) means composition f(u).")),
            Paragraph(Text("The operator mk forms a series from its coefficient function. "
                + "The function catalan is Mathlib's natural Catalan sequence, natCast(Z) "
                + "is Nat.castRingHom(Z), and intCast(ZMod(2)) is Int.castRingHom(ZMod(2)). "
                + "The operator map applies the indicated ring homomorphism to every "
                + "coefficient. Thus the binary Catalan formula is an equality in ZMod(2).")),
            Node("catalanSeries", "The shifted Catalan series", CatalanDefinition(),
                "D is Mathlib's Catalan series mapped to integer coefficients, and C is "
                + "its product with X. This fixes the shift in the OEIS equation.",
                DescribeRole.Definition),
            Node("catalan_equation", "The Catalan equation and normalization",
                Disp(CatalanNormalized()),
                "Mapping Mathlib's Catalan identity to the integers and multiplying "
                + "by X gives the quadratic equation. The shift gives zero constant "
                + "coefficient and linear coefficient one."),
            Node("catalan_unique", "Uniqueness of the shifted Catalan series", CatalanUnique(),
                "Subtract two quadratic equations. Their difference is annihilated "
                + "by 1-f-C, whose constant coefficient is one. This factor is a unit, "
                + "so the difference vanishes."),
            Node("generatingSeries", "Construction of the normalized solution", GeneratingDefinition(),
                "The displayed recursion defines the auxiliary approximations B(r). "
                + "The substitution argument is divisible by X squared. Consequently "
                + "agreement below degree r, for r at least one, gains a degree under "
                + "the recursion. The diagonal coefficients stabilize and define A.",
                DescribeRole.Definition),
            Node("a", "The coefficient sequence", Disp(Seq(Bound("n", Naturals()),
                Equal(Call("a", N()), Coefficient(N(), A())))),
                "The integer a(n) is the degree-n coefficient of A.", DescribeRole.Definition),
            Node("generating_equation", "The exact OEIS functional equation",
                Disp(GeneratingNormalized()),
                "The stabilized series B satisfies B=D subst(B,X squared times B times D). "
                + "With A=XB and C=XD, this identity gives A squared equal to subst(A,AC), "
                + "together with both normalization conditions."),
            Node("generating_unique", "Uniqueness of the normalized integer solution",
                GeneratingUnique(),
                "Factor any normalized solution as Xb. The constant coefficient of b "
                + "is one, so b is a unit. Cancel X squared and b from the functional "
                + "equation to obtain the same fixed-point equation. Degree contraction "
                + "then proves equality with the constructed solution."),
            Node("binary_catalan", "Binary support of the shifted Catalan series", BinaryCatalan(),
                "In characteristic two, squaring a series substitutes X squared. "
                + "The Catalan equation therefore sends each even positive index to "
                + "half that index; odd indices above one have zero coefficient. "
                + "Strong induction gives coefficient one exactly at powers of two."),
            Node("hanna_conjecture", "The A374570 parity conjecture", Conjecture(),
                "Reduce the generating equation modulo two. Frobenius gives "
                + "subst(A,X squared)=subst(A,AC). The compositional inverse of the "
                + "normalized outer series cancels A, giving AC=X squared. The Catalan "
                + "identity gives C(1+C)=X. Factoring C as X times a unit permits "
                + "cancellation, yielding A=X(1+C). Above degree one, the coefficients "
                + "are therefore odd exactly when the preceding index is a power of two.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a374570-catalan-composition-square-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a374570-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula X() => F.Id("X");
    private static Formula A() => F.Id("A");
    private static Formula Catalan() => F.Id("C");
    private static Formula UnitCatalan() => F.Id("D");
    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
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
    private static Formula Compose(Formula f, Formula u) => Call("subst", f, u);
    private static Formula CatalanEquation(Formula f) => Equal(f, Add(X(), Power(f, D(2))));
    private static Formula Equation(Formula f) =>
        Equal(Power(f, D(2)), Compose(f, Mul(f, Catalan())));
    private static Formula PowerIndex(Formula n, bool shifted) => Seq(
        Exists, Sp, K(), Colon, Sp, Naturals(), Comma, Sp,
        Equal(n, shifted ? Add(Power(D(2), K()), D(1)) : Power(D(2), K())));

    private static Formula CatalanDefinition() => Disp(new Formula.Aligned([
        Equal(UnitCatalan(), Call("map", Call("natCast", Integers()), Call("mk", Named("catalan")))),
        Equal(Catalan(), Mul(X(), UnitCatalan()))
    ]));

    private static Formula CatalanNormalized() => Conjunction(Equal(Constant(Catalan()), D(0)),
        Conjunction(Equal(Coefficient(D(1), Catalan()), D(1)), CatalanEquation(Catalan())));

    private static Formula CatalanUnique() => Disp(Seq(Bound("f", Series()),
        Implication(Equal(Constant(F.Id("f")), D(0)),
            Implication(CatalanEquation(F.Id("f")), Equal(F.Id("f"), Catalan())))));

    private static Formula GeneratingDefinition()
    {
        var r = F.Id("r");
        var br = Call("B", r);
        return Disp(new Formula.Aligned([
            Equal(Call("B", D(0)), D(1)),
            Seq(Bound("r", Naturals()), Equal(Call("B", Add(r, D(1))),
                Mul(UnitCatalan(), Compose(br, Mul(Mul(Power(X(), D(2)), br), UnitCatalan()))))),
            Equal(A(), Mul(X(), Call("mk", Lambda("n", Coefficient(N(), Call("B", N()))))))
        ]));
    }

    private static Formula GeneratingNormalized() => Conjunction(Equal(Constant(A()), D(0)),
        Conjunction(Equal(Coefficient(D(1), A()), D(1)), Equation(A())));

    private static Formula GeneratingUnique() => Disp(Seq(Bound("f", Series()),
        Implication(Equal(Constant(F.Id("f")), D(0)),
            Implication(Equal(Coefficient(D(1), F.Id("f")), D(1)),
                Implication(Equation(F.Id("f")), Equal(F.Id("f"), A()))))));

    private static Formula BinaryCatalan() => Disp(Seq(Bound("n", Naturals()),
        Parenthesized(Equal(Coefficient(N(), Call("map", Call("intCast", Call("ZMod", D(2))),
            Catalan())), D(1))), Sp, Iff, Sp, Parenthesized(PowerIndex(N(), false))));

    private static Formula Conjecture() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Lt, Sp, N()),
            Parenthesized(Seq(Call("Odd", Call("a", N())), Sp, Iff, Sp,
                Parenthesized(PowerIndex(N(), true)))))));
}
