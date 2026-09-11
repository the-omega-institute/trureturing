using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class ThreeFourIterateProductModSixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/ThreeFourIterateProductModSix.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2026a396797");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive-index coefficient of OEIS A396797 is congruent to one modulo six.",
        H("Hanna's Three-Four Iterate Product Congruence"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2026a396797 defines its generating series "
                + "by A(x)=x+A^3(x)A^4(x) and conjectures that a(n)=1 modulo 6 for n at "
                + "least one. Superscripts in this equation denote compositional iterates. "
                + "The construction below proves existence and uniqueness of a zero-constant "
                + "integer series satisfying this equation.")),
            Paragraph(Text("PowerSeries(R) is the formal power-series ring over R, and X is "
                + "its indeterminate. Ring parameters implicit in Lean are displayed explicitly. "
                + "The operations iterate and mobius are those of CompositionalIterateCongruence: "
                + "iterate(f,0)=X, and each successor substitutes f into the preceding iterate; "
                + "mobius(c) is X times the geometric series with coefficients c^n. All "
                + "indices are natural numbers, mk constructs a series from its coefficients, "
                + "and the final remainder is integer remainder.")),
            Node("a", "The integer coefficient sequence", CoefficientFormula(),
                "Here approx is local notation for successive applications of the displayed "
                + "transformation, starting at the zero integer series. Its degree-n coefficient "
                + "has stabilized by approximation n+1, which defines a(n).",
                DescribeRole.Definition),
            Node("generatingSeries", "The generating series", GeneratingFormula(),
                "The integer generating series is constructed with coefficient function a.",
                DescribeRole.Definition),
            Node("generating_equation", "Existence with the defining equation", EquationFormula(),
                "Substitution preserves agreement below degree d for zero-constant series. "
                + "For any two compositional iterate counts, the difference of their products "
                + "splits into two terms, each divisible by X^(d+1). This degree improvement "
                + "stabilizes the approximations. Their diagonal coefficient sequence has "
                + "zero constant term and satisfies the entire functional equation."),
            Node("generating_unique", "Uniqueness of the integer solution", UniqueFormula(),
                "For two zero-constant fixed points, induction on the degree applies the "
                + "product comparison repeatedly. Every coefficient agrees, so every integer "
                + "series B satisfying the two displayed hypotheses equals generatingSeries."),
            Node("mod_six_fixed", "A geometric fixed point modulo six", FixedFormula(),
                "The geometric-family iteration formula gives mobius(3) and mobius(4). "
                + "In ZMod(6), (1-3X)(1-4X)=1-X because 3+4=1 and 3 times 4 is zero. "
                + "Multiplying by these denominators and cancelling the unit 1-X proves "
                + "the identity of formal power series."),
            Node("hanna_conjecture", "The first A396797 conjecture", CongruenceFormula(),
                "Map the integer generating equation to ZMod(6). Coefficient mapping commutes "
                + "with substitution, and the degree comparison proves uniqueness over this "
                + "ring as well. The mapped series therefore equals mobius(1), whose "
                + "positive-degree coefficients are all one. The integer-cast congruence "
                + "equivalence gives the displayed remainder. The conjecture is recorded "
                + "in hanna2026a396797.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396797-three-four-iterate-product-mod-six"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a396797-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula ModSix() => Call("ZMod", D(6));
    private static Formula Series(Formula ring) => Call("PowerSeries", ring);
    private static Formula X() => F.Id("X");
    private static Formula Generating() => Named("generatingSeries");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula Iter(Formula ring, Formula series, Formula count) =>
        Call("iterate", ring, series, count);
    private static Formula Approx(Formula depth) => Call("approx", Integers(), depth);
    private static Formula MobiusOne() => Call("mobius", ModSix(), D(1));
    private static Formula RightSide(Formula ring, Formula series) =>
        Add(X(), Mul(Iter(ring, series, D(3)), Iter(ring, series, D(4))));

    private static Formula CoefficientFormula() => Disp(new Formula.Aligned([
        Seq(Bound("n", Naturals()), Equal(Call("a", F.Id("n")),
            Call("coeff", F.Id("n"), Approx(Add(F.Id("n"), D(1)))))),
        Equal(Approx(D(0)), D(0)),
        Seq(Bound("d", Naturals()), Equal(Approx(Add(F.Id("d"), D(1))),
            RightSide(Integers(), Approx(F.Id("d")))))
    ]));

    private static Formula GeneratingFormula() => Disp(Equal(Generating(), Call("mk", Named("a"))));

    private static Formula EquationFormula() => Disp(Seq(
        Parenthesized(Equal(Call("constantCoeff", Generating()), D(0))), Sp, Land, Sp,
        Parenthesized(Equal(Generating(), RightSide(Integers(), Generating())))));

    private static Formula UniqueFormula() => Disp(Seq(Bound("B", Series(Integers())),
        Implication(Equal(Call("constantCoeff", F.Id("B")), D(0)),
            Implication(Equal(F.Id("B"), RightSide(Integers(), F.Id("B"))),
                Equal(F.Id("B"), Generating())))));

    private static Formula FixedFormula() => Disp(Equal(MobiusOne(), RightSide(ModSix(), MobiusOne())));

    private static Formula CongruenceFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Le, Sp, F.Id("n")),
            Equal(new Formula.Modulo(Call("a", F.Id("n")), D(6)), D(1)))));
}
