using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CompositionalIterateCongruenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/CompositionalIterateCongruence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2026a396807");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive-index coefficient of OEIS A396807 is congruent to one modulo ten.",
        H("Hanna's Compositional-Iterate Congruence"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's OEIS entry of June 16, 2026 uses superscripts "
                + "for compositional iteration, not ordinary powers. The sequence below is "
                + "constructed over the integers. Its generating series has zero constant "
                + "term and satisfies exactly the defining equation; the uniqueness theorem "
                + "identifies it without assuming that a fixed point exists.")),
            Paragraph(Text("Ring parameters are displayed explicitly, including those implicit "
                + "in Lean. PowerSeries(R) is the formal power-series ring, X its indeterminate, "
                + "and subst(f,g) denotes f composed with g. The operator mk constructs a "
                + "series from its coefficient function; mk(1) uses the constant function one. "
                + "Rescaling multiplies coefficient n by the nth power of its parameter. "
                + "The final remainder is integer remainder, and all indices are natural numbers.")),
            Node("iterate", "Compositional iteration", IterateFormula(),
                "The zeroth iterate is the identity series X. Each successor substitutes "
                + "the original series into the previous iterate. On zero-constant series "
                + "this is the usual compositional iteration.", DescribeRole.Definition),
            Node("step", "The defining transformation", StepFormula(),
                "The fifth and sixth compositional iterates are multiplied as power series. "
                + "Adding X gives the transformation whose fixed point defines the sequence.",
                DescribeRole.Definition),
            Node("fixed_unique", "Uniqueness by degree", UniqueFormula(),
                "Agreement below degree d is preserved by powers and by substitution of "
                + "zero-constant series. The difference of the two products is split into "
                + "two terms, each gaining an additional factor X. Thus step improves "
                + "agreement to degree d+1. Induction and coefficient extensionality prove "
                + "uniqueness over every commutative ring, including rings with zero divisors."),
            Node("approximation", "Successive approximations", ApproximationFormula(),
                "Start from zero and apply step repeatedly. The degree-contraction argument "
                + "proves that approximation d and every later approximation agree below d.",
                DescribeRole.Definition),
            Node("a", "The integer coefficient sequence", CoefficientFormula(),
                "Coefficient n is read from approximation n+1, where it has stabilized. "
                + "This construction does not choose an assumed fixed point.", DescribeRole.Definition),
            Node("generatingSeries", "The generating series", GeneratingFormula(),
                "The generating series has coefficient function a.", DescribeRole.Definition),
            Node("generating_equation", "Existence with the OEIS equation", EquationFormula(),
                "The stabilized coefficients agree to every finite degree with sufficiently "
                + "late approximations. Applying degree contraction once more gives the "
                + "generating equation. Together with fixed_unique, this characterizes a "
                + "as the unique integer coefficient sequence with zero constant term "
                + "and the stated compositional equation."),
            Node("mobius", "The geometric family", MobiusFormula(),
                "This series is X times the geometric series with parameter c, equivalently "
                + "X/(1-cX). The denominator has constant term one and is a unit over every "
                + "commutative ring; no field division is assumed.", DescribeRole.Definition),
            Node("mobius_iterate", "Iterating the geometric family", MobiusIterateFormula(),
                "Rescaling Mathlib's geometric-series identity gives the denominator identity. "
                + "Apply substitution to it and multiply by the inner denominator to prove "
                + "that composition adds parameters. Induction gives the displayed formula "
                + "for every parameter and every iteration count."),
            Node("mod_ten_fixed", "A fixed point modulo ten", FixedFormula(),
                "In ZMod(10), the product (1-5X)(1-6X) equals 1-X: the quadratic "
                + "coefficient 30 vanishes and 11 equals 1. The geometric-family iteration "
                + "formula and cancellation of the unit denominator prove the fixed-point "
                + "identity for the entire unbounded series."),
            Node("coefficient_congruence", "The A396807 conjecture", CongruenceFormula(),
                "Map the constructed integer generating equation to ZMod(10). Substitution "
                + "commutes with this map. Uniqueness identifies the mapped series with "
                + "mobius(1), whose positive-degree coefficients are all one. Mathlib's "
                + "integer-cast congruence equivalence gives the integer remainder statement. "
                + "The conjecture is from the cited entry; its proof is derived here.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396807-compositional-iterate-congruence"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a396807-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Ring() => F.Id("R");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula ModTen() => Call("ZMod", D(1, 0));
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
    private static Formula Context() => Seq(Bound("R", F.Id("Type")),
        OpenBracket, Call("CommRing", Ring()), CloseBracket, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula Iter(Formula ring, Formula series, Formula count) =>
        Call("iterate", ring, series, count);
    private static Formula Step(Formula ring, Formula series) => Call("step", ring, series);
    private static Formula Approx(Formula ring, Formula depth) => Call("approximation", ring, depth);
    private static Formula Mobius(Formula ring, Formula parameter) => Call("mobius", ring, parameter);
    private static Formula RightSide(Formula ring, Formula series) =>
        Add(X(), Mul(Iter(ring, series, D(5)), Iter(ring, series, D(6))));

    private static Formula IterateFormula()
    {
        Formula series = F.Id("series");
        Formula count = F.Id("count");
        return Disp(new Formula.Aligned([
            Seq(Context(), Bound("series", Series(Ring())), Bound("count", Naturals())),
            Equal(Iter(Ring(), series, D(0)), X()),
            Equal(Iter(Ring(), series, Add(count, D(1))),
                Call("subst", Iter(Ring(), series, count), series))
        ]));
    }

    private static Formula StepFormula() => Disp(Seq(Context(), Bound("series", Series(Ring())),
        Equal(Step(Ring(), F.Id("series")), RightSide(Ring(), F.Id("series")))));

    private static Formula UniqueFormula()
    {
        Formula left = F.Id("left");
        Formula right = F.Id("right");
        return Disp(new Formula.Aligned([
            Seq(Context(), Bound("left", Series(Ring())), Bound("right", Series(Ring()))),
            Implication(Equal(Call("constantCoeff", left), D(0)),
                Implication(Equal(Call("constantCoeff", right), D(0)),
                    Implication(Equal(left, Step(Ring(), left)),
                        Implication(Equal(right, Step(Ring(), right)), Equal(left, right)))))
        ]));
    }

    private static Formula ApproximationFormula() => Disp(new Formula.Aligned([
        Seq(Context(), Bound("depth", Naturals())),
        Equal(Approx(Ring(), D(0)), D(0)),
        Equal(Approx(Ring(), Add(F.Id("depth"), D(1))), Step(Ring(), Approx(Ring(), F.Id("depth"))))
    ]));

    private static Formula CoefficientFormula() => Disp(Seq(Bound("index", Naturals()),
        Equal(Call("a", F.Id("index")), Call("coeff", F.Id("index"),
            Approx(Integers(), Add(F.Id("index"), D(1)))))));

    private static Formula GeneratingFormula() => Disp(Equal(Generating(), Call("mk", Named("a"))));

    private static Formula EquationFormula() => Disp(Seq(
        Parenthesized(Equal(Call("constantCoeff", Generating()), D(0))), Sp, Land, Sp,
        Parenthesized(Equal(Generating(), RightSide(Integers(), Generating())))));

    private static Formula MobiusFormula() => Disp(Seq(Context(), Bound("parameter", Ring()),
        Equal(Mobius(Ring(), F.Id("parameter")),
            Mul(X(), Call("rescale", F.Id("parameter"), Call("mk", D(1)))))));

    private static Formula MobiusIterateFormula() => Disp(new Formula.Aligned([
        Seq(Context(), Bound("parameter", Ring()), Bound("count", Naturals())),
        Equal(Iter(Ring(), Mobius(Ring(), F.Id("parameter")), F.Id("count")),
            Mobius(Ring(), Mul(Call("cast", F.Id("count"), Ring()), F.Id("parameter"))))
    ]));

    private static Formula FixedFormula() => Disp(Equal(Mobius(ModTen(), D(1)),
        RightSide(ModTen(), Mobius(ModTen(), D(1)))));

    private static Formula CongruenceFormula() => Disp(Seq(Bound("index", Naturals()),
        Implication(Seq(D(1), Sp, Le, Sp, F.Id("index")),
            Equal(new Formula.Modulo(Call("a", F.Id("index")), D(1, 0)), D(1)))));
}
