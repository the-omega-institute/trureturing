using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class IterateProductTwoThreeModFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/IterateProductTwoThreeModFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a396099");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unique integer series of OEIS A396099 satisfies all four congruence conjectures.",
        H("Hanna's Two-Three Iterate Product Congruences"),
        Blocks(
            Paragraph(Text("The entry cited in hanna2026a396099 defines A(x) by "
                + "A(x)=x+A^2(x)A^3(x). Its FORMULA and PROG interpret the superscripts "
                + "as compositional iterates. It conjectures oddness at every positive "
                + "index, the repeating residues [1,3,3,1] beginning at index three, "
                + "vanishing coefficients of A(A(x)) modulo four above degree two, "
                + "and residue two for A(x)-x*A(A(A(x))) above degree two.")),
            Paragraph(Text("PowerSeries(R) is the formal power-series ring over R, X is "
                + "its indeterminate, coeff extracts a coefficient, and mk constructs a "
                + "series from its coefficient function. The operations iterate and mobius "
                + "are those of CompositionalIterateCongruence: iterate(f,0)=X, "
                + "iterate(f,k+1)=subst(iterate(f,k),f), and mobius(c) is X times the "
                + "geometric series with coefficients c^n. Ring parameters implicit in "
                + "Lean are displayed explicitly for these operations. The operation "
                + "invOfUnit(g,1) is the formal inverse with prescribed constant unit one; "
                + "the displayed denominator has constant coefficient one. All indices "
                + "are natural numbers. Remainders of a and integer-series coefficients "
                + "are integer remainders; the remainder of n is natural remainder.")),
            Node("a", "The integer coefficient sequence", CoefficientFormula(),
                "The local notation approx denotes iteration of the displayed "
                + "transformation from the zero integer series. Its degree-n coefficient "
                + "stabilizes by approximation n+1, defining a(n).", DescribeRole.Definition),
            Node("generatingSeries", "The integer generating series", GeneratingFormula(),
                "The generating series has coefficient function a.", DescribeRole.Definition),
            Node("generating_equation", "The equation and normalization", EquationFormula(),
                "Substitution preserves agreement below degree d for zero-constant series. "
                + "The difference of the two iterate products splits into terms divisible "
                + "by X^(d+1), since both factors have zero constant coefficient. This "
                + "improvement stabilizes the approximations and proves the equation. "
                + "The product contributes neither a constant nor a linear coefficient."),
            Node("generating_unique", "Uniqueness of the integer solution", UniqueFormula(),
                "The product comparison improves agreement of any two zero-constant "
                + "fixed points by one degree. Induction proves equality of every "
                + "coefficient, so every B satisfying the two hypotheses equals generatingSeries."),
            Node("mod_four_identity", "The rational reduction modulo four", ReductionFormula(),
                "Write D=(1-X)(1+X^2), N=X+X^3+2X^4, and F=N*invOfUnit(D,1). "
                + "Substitute F into F*D=N, clear the unit denominator D^4, and reduce "
                + "the polynomial identity in characteristic four. This proves "
                + "subst(F,F)=X+2X^2; consequently iterate(F,3)=F+2F^2. Clearing D^2 "
                + "proves F=X+(X+2X^2)(F+2F^2). Mapping commutes with substitution, "
                + "so degree comparison identifies the reduced integer solution with F. "
                + "A final unit cancellation gives the displayed rational form."),
            Node("all_odd", "Every positive-index term is odd", OddFormula(),
                "The rational reduction is also X*mk(1)+2X^4(1+X)*subst(mk(1),X^4). "
                + "The first two positive coefficients are one. The higher coefficients "
                + "have residue one or three modulo four, so every positive-index "
                + "integer coefficient is odd.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source)),
            Node("hanna_conjecture", "The period-four coefficient pattern", PatternFormula(),
                "The identity D*(1+X)=1-X^4 rewrites F as "
                + "X*mk(1)+2X^4(1+X)*subst(mk(1),X^4). The last geometric series "
                + "has coefficient one exactly at multiples of four. Coefficient "
                + "extraction gives residue one when n mod 4 is two or three, and "
                + "three otherwise, for every n greater than two. This is the pattern "
                + "[1,3,3,1] starting at n=3 in hanna2026a396099.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396099-iterate-product-two-three-mod-four"),
                    ResolutionKind.Proved)),
            Node("iterate_two_mod_four", "The second iterate above degree two", IterateFormula(),
                "Map the second iterate through the canonical integer homomorphism to "
                + "ZMod(4). Substitution commutes with mapping, and the rational "
                + "composition identity gives X+2X^2. Every coefficient above degree "
                + "two therefore has integer remainder zero modulo four.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source)),
            Node("shift_mod_four", "The shifted third-iterate difference", ShiftFormula(),
                "Clearing D^2 and the unit 1-X gives "
                + "F-X*(F+2F^2)=X+2X^3*mk(1). The third iterate is F+2F^2, "
                + "so mapping the integer difference gives this geometric expression. "
                + "Its coefficient is two in every degree greater than two.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a396099-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula ModFour() => Call("ZMod", D(4));
    private static Formula X() => F.Id("X");
    private static Formula N() => F.Id("n");
    private static Formula A() => Named("generatingSeries");
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
    private static Formula Iter(Formula ring, Formula series, Formula count) =>
        Call("iterate", ring, series, count);
    private static Formula Approx(Formula depth) => Call("approx", Integers(), depth);
    private static Formula RightSide(Formula series) => Add(X(),
        Mul(Iter(Integers(), series, D(2)), Iter(Integers(), series, D(3))));
    private static Formula AboveTwo() => Seq(D(2), Sp, Lt, Sp, N());
    private static Formula Remainder(Formula value) => new Formula.Modulo(value, D(4));

    private static Formula CoefficientFormula() => Disp(new Formula.Aligned([
        Seq(Bound("n", Naturals()), Equal(Call("a", N()),
            Call("coeff", N(), Approx(Add(N(), D(1)))))),
        Equal(Approx(D(0)), D(0)),
        Seq(Bound("d", Naturals()), Equal(Approx(Add(F.Id("d"), D(1))),
            RightSide(Approx(F.Id("d")))))
    ]));

    private static Formula GeneratingFormula() => Disp(Equal(A(), Call("mk", Named("a"))));

    private static Formula EquationFormula() => Disp(And(
        Equal(Call("constantCoeff", A()), D(0)), And(
            Equal(Call("coeff", D(1), A()), D(1)), Equal(A(), RightSide(A())))));

    private static Formula UniqueFormula() => Disp(Seq(Bound("B", Call("PowerSeries", Integers())),
        Implication(Equal(Call("constantCoeff", F.Id("B")), D(0)),
            Implication(Equal(F.Id("B"), RightSide(F.Id("B"))), Equal(F.Id("B"), A())))));

    private static Formula ReductionFormula() => Disp(Equal(
        Call("map", Call("intCastRingHom", ModFour()), A()),
        Add(Call("mobius", ModFour(), D(1)),
            Mul(Mul(D(2), Power(X(), D(4))), Call("invOfUnit",
                Mul(Subtract(D(1), X()), Add(D(1), Power(X(), D(2)))), D(1))))));

    private static Formula OddFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Le, Sp, N()), Call("Odd", Call("a", N())))));

    private static Formula PatternFormula()
    {
        Formula condition = Seq(Equal(Remainder(N()), D(3)), Sp, Lor, Sp,
            Equal(Remainder(N()), D(2)));
        Formula pattern = Parenthesized(Seq(Named("if"), Sp, Parenthesized(condition), Sp,
            Named("then"), Sp, D(1), Sp, Named("else"), Sp, D(3)));
        return Disp(Seq(Bound("n", Naturals()),
            Implication(AboveTwo(), Equal(Remainder(Call("a", N())), pattern))));
    }

    private static Formula IterateFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(AboveTwo(), Equal(Remainder(
            Call("coeff", N(), Iter(Integers(), A(), D(2)))), D(0)))));

    private static Formula ShiftFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(AboveTwo(), Equal(Remainder(Call("coeff", N(),
            Subtract(A(), Mul(X(), Iter(Integers(), A(), D(3)))))), D(2)))));
}
