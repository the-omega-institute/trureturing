using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CatalanShiftSquareModFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/CatalanShiftSquareModFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2026a393172");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of OEIS A393172 above degree one are two modulo four exactly at powers of two, and zero otherwise.",
        H("Catalan Inversion and Hanna's Mod-Four Conjecture"),
        Blocks(
            Paragraph(Text("The generating equation and conjecture are recorded in "
                + "hanna2026a393172. Write A for generatingSeries and C for "
                + "CatalanCompositionSquareParity.catalanSeries, the integer series "
                + "with zero constant coefficient satisfying C=X+C squared. The "
                + "auxiliary B(r) are integer series, and all indices and exponents "
                + "are natural numbers. X is the indeterminate.")),
            Paragraph(Text("The operator subst(f,u) means composition f(u). The "
                + "operator mk forms a series from its coefficient function. The "
                + "operator map applies its first argument, a ring homomorphism, "
                + "to the coefficients of its second argument. Here intCast(ZMod(2)) "
                + "denotes Int.castRingHom(ZMod(2)). Remainders of a(n) are integer "
                + "remainders; remainder zero modulo four is equivalent to divisibility by four.")),
            Node("a", "The stabilized integer coefficients", CoefficientDefinition(),
                "The displayed B recursion is the auxiliary approximation sequence. "
                + "Composition with C preserves agreement below a degree, and squaring "
                + "zero-constant series gains a degree. Thus each diagonal coefficient "
                + "used to define a(n) has stabilized.", DescribeRole.Definition),
            Node("generatingSeries", "The generating series",
                Disp(Equal(A(), Call("mk", Named("a")))),
                "The degree-n coefficient of A is a(n).", DescribeRole.Definition),
            Node("generating_equation", "The exact generating equation and normalization",
                Disp(Conjunction(Equal(Constant(A()), D(0)),
                    Conjunction(Equal(Coefficient(D(1), A()), D(1)), Equation(A())))),
                "The stabilized series satisfies A=C+subst(A,C) squared. The Catalan "
                + "equation identifies C as the compositional inverse of X-X squared. "
                + "Composing the fixed-point identity with X-X squared gives the OEIS "
                + "equation. The constant coefficient is zero, and the quadratic term "
                + "has no linear coefficient, so the linear coefficient is one."),
            Node("generating_unique", "Uniqueness among zero-constant integer series",
                UniqueFormula(),
                "Compose the equation for f with C to obtain f=C+subst(f,C) squared. "
                + "The difference of two squares factors into a difference times a "
                + "zero-constant sum. Induction on the degree therefore proves agreement "
                + "of any two fixed points. No separate linear-coefficient hypothesis is needed."),
            Node("mod_two_identity", "The first reduction",
                Disp(Equal(Call("map", Call("intCast", Call("ZMod", D(2))), A()), X())),
                "Reducing the exact generating equation modulo two gives an equation "
                + "also satisfied by X. If the two series differed, choose their least "
                + "differing coefficient. Degree contraction forces equality at that "
                + "coefficient as well, a contradiction. Consequently every coefficient "
                + "of A-X is even."),
            Node("hanna_conjecture", "The A393172 conjecture", ConjectureFormula(),
                "Define the integer series H coefficientwise by dividing A-X by two. "
                + "The exact equation becomes subst(H,X-X squared)=X squared+2XH+2H squared. "
                + "Modulo two, composition with the reduced Catalan series gives H=C squared. "
                + "Above degree one, C squared and C have the same coefficients. The "
                + "binary_catalan theorem identifies coefficient one precisely at powers "
                + "of two. Since a(n) is twice the corresponding coefficient of H, "
                + "the two stated remainder equivalences follow.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a393172-catalan-shift-square-mod-four"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a393172-" + name.Replace('_', '-').ToLowerInvariant()),
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
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Coefficient(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula Constant(Formula f) => Call("constantCoeff", f);
    private static Formula Compose(Formula f, Formula u) => Call("subst", f, u);
    private static Formula Equation(Formula f) =>
        Equal(Compose(f, Subtract(X(), Power(X(), D(2)))), Add(X(), Power(f, D(2))));
    private static Formula PowerIndex() => Seq(Exists, Sp, K(), Colon, Sp, Naturals(), Comma, Sp,
        Equal(N(), Power(D(2), K())));

    private static Formula CoefficientDefinition()
    {
        var r = F.Id("r");
        return Disp(new Formula.Aligned([
            Equal(Call("B", D(0)), D(0)),
            Seq(Bound("r", Naturals()), Equal(Call("B", Add(r, D(1))),
                Add(Catalan(), Power(Compose(Call("B", r), Catalan()), D(2))))),
            Seq(Bound("n", Naturals()), Equal(Call("a", N()),
                Coefficient(N(), Call("B", Add(N(), D(1))))))
        ]));
    }

    private static Formula UniqueFormula() => Disp(Seq(Bound("f", Series()),
        Implication(Equal(Constant(F.Id("f")), D(0)),
            Implication(Equation(F.Id("f")), Equal(F.Id("f"), A())))));

    private static Formula ConjectureFormula()
    {
        var remainder = new Formula.Modulo(Call("a", N()), D(4));
        var two = Seq(Parenthesized(Equal(remainder, D(2))), Sp, Iff, Sp,
            Parenthesized(PowerIndex()));
        var zero = Seq(Parenthesized(Equal(remainder, D(0))), Sp, Iff, Sp,
            Parenthesized(Seq(Neg, Sp, Parenthesized(PowerIndex()))));
        return Disp(Seq(Bound("n", Naturals()),
            Implication(Seq(D(1), Sp, Lt, Sp, N()),
                Parenthesized(Conjunction(two, zero)))));
    }
}
