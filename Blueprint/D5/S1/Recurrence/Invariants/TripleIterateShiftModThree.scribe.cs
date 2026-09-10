using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class TripleIterateShiftModThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/TripleIterateShiftModThree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2026a396102");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive-index coefficient of OEIS A396102 is congruent to one modulo three.",
        H("Hanna's Triple Iterate Shift Congruence"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2026a396102 defines A(x)=x+... by "
                + "A(A(A(x)))=(1+x)A(A(x)) and conjectures that a(n)=1 modulo three "
                + "for every n at least one. The construction below proves existence "
                + "and uniqueness of an integer series with constant coefficient zero "
                + "and linear coefficient one satisfying this equation.")),
            Paragraph(Text("PowerSeries(R) denotes the formal power-series ring over R, "
                + "and X is its indeterminate. The ring argument of iterate and mobius, "
                + "implicit in Lean, is displayed explicitly. These operations come from "
                + "CompositionalIterateCongruence: iterate(f,0)=X, and each successor "
                + "substitutes f into the preceding iterate; mobius(c) is X times the "
                + "geometric series with coefficients c^n. Indices are natural numbers, "
                + "mk constructs a series from its coefficient function, and the final "
                + "remainder is integer remainder.")),
            Node("a", "The integer coefficient sequence", CoefficientFormula(),
                "The local notation approximation denotes the integer series defined by "
                + "the displayed iteration, starting at X. Agreement below degree d, "
                + "for d at least two, improves to agreement below degree d+1 after "
                + "one step. Thus the diagonal coefficient defines a(n).",
                DescribeRole.Definition),
            Node("generatingSeries", "The generating series", GeneratingFormula(),
                "The integer series is constructed with coefficient function a.",
                DescribeRole.Definition),
            Node("generating_equation", "Existence and the functional equation", EquationFormula(),
                "For n greater than one and two zero-constant series agreeing below "
                + "degree n with linear coefficient one, the difference at degree n of "
                + "the j-th compositional iterates "
                + "is j times the original coefficient difference. The correction step "
                + "therefore cancels this difference with multiplier 1+2-3=0; the "
                + "factor X uses only the preceding coefficient. The stabilized "
                + "coefficients form a fixed point of the correction step, which is "
                + "exactly the displayed functional equation."),
            Node("generating_unique", "Uniqueness of the normalized integer solution", UniqueFormula(),
                "Any two solutions satisfy the correction fixed-point identity. Their "
                + "constant and linear coefficients agree. Applying degree contraction "
                + "inductively proves agreement at every degree, hence equality."),
            Node("mod_three_fixed", "The geometric solution modulo three", FixedFormula(),
                "The geometric-family iteration identity gives mobius(3)=X and "
                + "mobius(2) for the third and second iterates over ZMod(3). Since "
                + "-2=1 in that ring, the geometric denominator of mobius(2) is 1+X. "
                + "Multiplication by this denominator gives X, proving the equation."),
            Node("hanna_conjecture", "Hanna's A396102 conjecture", CongruenceFormula(),
                "Map the integer generating equation into ZMod(3). Mapping coefficients "
                + "commutes with substitution. The degree comparison proves uniqueness "
                + "over this ring too, so the mapped series equals mobius(1). Its "
                + "positive-degree coefficients are all one. The integer-cast "
                + "congruence equivalence gives the claimed remainder, as conjectured "
                + "in hanna2026a396102.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396102-triple-iterate-shift-mod-three"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a396102-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula ModThree() => Call("ZMod", D(3));
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
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula Iter(Formula ring, Formula series, Formula count) =>
        Call("iterate", ring, series, count);
    private static Formula Approx(Formula depth) => Call("approximation", Integers(), depth);
    private static Formula MobiusOne() => Call("mobius", ModThree(), D(1));
    private static Formula RightSide(Formula ring, Formula series) =>
        Mul(Parenthesized(Add(D(1), X())), Iter(ring, series, D(2)));
    private static Formula Equation(Formula ring, Formula series) =>
        Equal(Iter(ring, series, D(3)), RightSide(ring, series));
    private static Formula Step(Formula series) =>
        Subtract(Parenthesized(Add(series, RightSide(Integers(), series))),
            Iter(Integers(), series, D(3)));

    private static Formula CoefficientFormula() => Disp(new Formula.Aligned([
        Seq(Bound("n", Naturals()), Equal(Call("a", F.Id("n")),
            Call("coeff", F.Id("n"), Approx(F.Id("n"))))),
        Equal(Approx(D(0)), X()),
        Seq(Bound("d", Naturals()), Equal(Approx(Add(F.Id("d"), D(1))),
            Step(Approx(F.Id("d")))))
    ]));

    private static Formula GeneratingFormula() => Disp(Equal(Generating(), Call("mk", Named("a"))));

    private static Formula EquationFormula() => Disp(Seq(
        Parenthesized(Equal(Call("constantCoeff", Generating()), D(0))), Sp, Land, Sp,
        Parenthesized(Equal(Call("coeff", D(1), Generating()), D(1))), Sp, Land, Sp,
        Parenthesized(Equation(Integers(), Generating()))));

    private static Formula UniqueFormula() => Disp(Seq(Bound("f", Series(Integers())),
        Implication(Equal(Call("constantCoeff", F.Id("f")), D(0)),
            Implication(Equal(Call("coeff", D(1), F.Id("f")), D(1)),
                Implication(Equation(Integers(), F.Id("f")),
                    Equal(F.Id("f"), Generating()))))));

    private static Formula FixedFormula() => Disp(Equation(ModThree(), MobiusOne()));

    private static Formula CongruenceFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Le, Sp, F.Id("n")),
            Equal(new Formula.Modulo(Call("a", F.Id("n")), D(3)), D(1)))));
}
