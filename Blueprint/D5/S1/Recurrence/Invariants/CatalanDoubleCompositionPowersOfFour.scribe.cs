using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CatalanDoubleCompositionPowersOfFourDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/CatalanDoubleCompositionPowersOfFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2024a374568");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of OEIS A374568 are odd exactly at powers of four.",
        H("Double Catalan Composition and Powers of Four"),
        Blocks(
            Paragraph(Text("The generating equation and parity conjecture are recorded in "
                + "hanna2024a374568. Write A for generatingSeries and C for "
                + "CatalanCompositionSquareParity.catalanSeries, the shifted integer "
                + "Catalan series satisfying C=X+C squared. The coefficients a(n), the "
                + "series A and C, and the approximations B(r) are integer-valued. All "
                + "coefficient indices and exponents are natural numbers.")),
            Paragraph(Text("The operator subst(f,u) denotes composition f(u), and mk forms "
                + "a power series from its coefficient function. The operator map applies "
                + "a ring homomorphism coefficientwise; intCast(ZMod(2)) denotes "
                + "Int.castRingHom(ZMod(2)). In formulas involving this map, X denotes "
                + "the indeterminate over ZMod(2).")),
            Node("generatingSeries", "Construction of the integer series", GeneratingDefinition(),
                "The recursion starts at zero. Since every approximation has zero "
                + "constant coefficient, its squared composition gains one degree of "
                + "agreement at each step. The diagonal coefficients therefore stabilize "
                + "and define the integer series A.", DescribeRole.Definition),
            Node("a", "The coefficient sequence", Disp(Seq(Bound("n", Naturals()),
                Equal(Call("a", N()), Coefficient(N(), A())))),
                "The integer a(n) is the degree-n coefficient of A.", DescribeRole.Definition),
            Node("generating_equation", "The exact functional equation and normalization",
                Disp(Conjunction(Equal(Constant(A()), D(0)),
                    Conjunction(Equal(Coefficient(D(1), A()), D(1)), Equation(A())))),
                "The Catalan series is the compositional inverse of X-X squared. "
                + "Substituting X-X squared into the stabilized recursion gives the "
                + "displayed OEIS equation. The constant coefficient is zero, and the "
                + "square term contributes nothing to degree one."),
            Node("generating_unique", "Uniqueness of the integer solution", GeneratingUnique(),
                "Compose the equation with C to recover the same fixed-point recursion. "
                + "Induction on coefficient agreement proves that every zero-constant "
                + "solution equals A. No separate linear-coefficient hypothesis is needed."),
            Node("mod_two_identity", "Identification with the binary Catalan series",
                Disp(Equal(Compose(Reduce(A()), Add(X(), Power(X(), D(2)))), Reduce(Catalan()))),
                "After reduction modulo two, both substitution arguments become "
                + "X+X squared. Thus Y=subst(map(A),X+X squared) satisfies Y=X+Y squared. "
                + "The reduced Catalan series satisfies the same equation. Subtracting "
                + "these equations factors their difference by a series with constant "
                + "coefficient one, so the two solutions coincide."),
            Node("hanna_conjecture", "Hanna's powers-of-four parity conjecture", Conjecture(),
                "Write Cbar for the reduction of C. Since Cbar+Cbar squared=X, "
                + "composing the preceding identity with Cbar gives map(A)=Cbar(Cbar). "
                + "Put D=Cbar(Cbar). Composing the Catalan equation gives D=Cbar+D squared. "
                + "Squaring and using characteristic two cancels the middle square, "
                + "yielding D=X+D to the fourth power. Frobenius identifies the fourth "
                + "power with substitution of X to the fourth power. Strong induction "
                + "on the coefficient index now gives coefficient one exactly at powers "
                + "of four, which is equivalent to oddness of the integer coefficient.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a374568-catalan-double-composition-powers-of-four"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a374568-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula X() => F.Id("X");
    private static Formula A() => F.Id("A");
    private static Formula Catalan() => F.Id("C");
    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
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
    private static Formula Reduce(Formula f) =>
        Call("map", Call("intCast", Call("ZMod", D(2))), f);
    private static Formula Equation(Formula f) => Equal(X(),
        Subtract(Compose(f, Subtract(X(), Power(X(), D(2)))),
            Power(Compose(f, Add(X(), Power(X(), D(2)))), D(2))));

    private static Formula GeneratingDefinition()
    {
        var r = F.Id("r");
        return Disp(new Formula.Aligned([
            Equal(Call("B", D(0)), D(0)),
            Seq(Bound("r", Naturals()), Equal(Call("B", Add(r, D(1))),
                Add(Catalan(), Power(Compose(Call("B", r),
                    Compose(Add(X(), Power(X(), D(2))), Catalan())), D(2))))),
            Equal(A(), Call("mk", Lambda("n", Coefficient(N(), Call("B", Add(N(), D(1)))))))
        ]));
    }

    private static Formula GeneratingUnique() => Disp(Seq(Bound("f", Series()),
        Implication(Equal(Constant(F.Id("f")), D(0)),
            Implication(Equation(F.Id("f")), Equal(F.Id("f"), A())))));

    private static Formula Conjecture() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Le, Sp, N()),
            Parenthesized(Seq(Call("Odd", Call("a", N())), Sp, Iff, Sp,
                Parenthesized(Seq(Exists, Sp, K(), Colon, Sp, Naturals(), Comma, Sp,
                    Equal(N(), Power(D(4), K())))))))));
}
