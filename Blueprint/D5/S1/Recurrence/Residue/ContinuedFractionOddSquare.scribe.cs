using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class ContinuedFractionOddSquareDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2020a338636");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of the odd-square continued fraction in OEIS A338636 are divisible by eight above degree one.",
        H("Hanna's Odd-Square Continued Fraction"),
        Blocks(
            Paragraph(Text("The equation and mod-eight conjecture are recorded in "
                + "hanna2020a338636. All indices are natural numbers. PowerSeries(R) denotes "
                + "formal series over a commutative ring R, X is the formal variable, C embeds "
                + "a scalar, and coeff(n,A) is the degree-n coefficient. The ring argument of "
                + "finiteTail is displayed explicitly. The function cast(R,m) is the natural "
                + "number m viewed in R. The expression invOfUnit(A,1) is the formal inverse "
                + "with constant coefficient one; the denominator identities below justify "
                + "its use as division. Types may lie in any universe.")),
            Node("finiteTail", "Finite tails with a specified terminal denominator", TailFormula(),
                "There are d levels beginning at numerator (2j+1)^2*X. The terminal "
                + "denominator is A at index j+d. The outermost numerator in the defining "
                + "equation is X, and its denominator begins at j=1.", DescribeRole.Definition),
            Node("stabilization", "Increasing depth preserves the old coefficients", StableFormula(),
                "Induction on the old depth compares the two terminal chains. Inversion "
                + "of series with constant coefficient one preserves agreement, and each "
                + "multiplication by X gains one degree. The initial comparison is their "
                + "common constant coefficient. Thus a coefficient of index n is independent "
                + "of all depths at least n."),
            Node("a", "The stabilized integer coefficient sequence", CoefficientFormula(),
                "The auxiliary integer series P(m) is the private approximation at stage m. "
                + "It begins at one. The displayed coefficient rule gives the next series, "
                + "using tail depth k for its coefficient of index k. The transformation "
                + "gains one degree of agreement, so P(m) and every later approximation "
                + "agree through degree m. The diagonal coefficients therefore stabilize.",
                DescribeRole.Definition),
            Node("generatingSeries", "The integer generating series", SeriesFormula(),
                "PowerSeries.mk assembles the coefficient function a into a formal integer "
                + "series. Its coefficients agree with each approximation through that "
                + "approximation's stage.", DescribeRole.Definition),
            Node("generating_equation", "The continued-fraction equation at every finite depth", EquationFormula(),
                "Every finite tail has constant coefficient one and its displayed inverse "
                + "multiplies it to one. Stabilization identifies the coefficientwise "
                + "construction with the depth-d fraction through degree d+1. This is the "
                + "finite-depth interpretation of the continued fraction in hanna2020a338636."),
            Node("generating_unique", "Uniqueness of the normalized integer solution", UniqueFormula(),
                "The finite-depth equations make any normalized solution a fixed point "
                + "of the coefficient transformation defining P. If two input series agree "
                + "below degree n, their outputs agree below degree n+1. Induction gives "
                + "agreement at every degree and hence equality of the two series."),
            Node("hanna_conjecture", "Divisibility by eight above degree one", ConjectureFormula(),
                "Map the proved finite-depth equations to ZMod(8). Every odd square equals "
                + "one because two divides j*(j+1). For A=1+X, induction shows that a tail "
                + "of depth d agrees with one through degree d. Thus 1+X is the reduced "
                + "fixed point, and contraction uniqueness identifies it with the reduction "
                + "of generatingSeries. Its coefficients above degree one vanish.",
                provenance: AssessedProvenance.FromLiterature(Source),
                claim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a338636-continued-fraction-odd-square-mod-eight"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a338636-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula LessEqual(Formula left, Formula right) => Seq(left, Sp, Le, Sp, right);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula X() => F.Id("X");
    private static Formula Generating() => Named("generatingSeries");
    private static Formula Series(Formula ring) => Call("PowerSeries", ring);
    private static Formula Coeff(Formula n, Formula a) => Call("coeff", n, a);
    private static Formula Constant(Formula a) => Call("constantCoeff", a);
    private static Formula Inverse(Formula a) => Call("invOfUnit", a, D(1));
    private static Formula Tail(Formula ring, Formula a, Formula j, Formula d) =>
        Call("finiteTail", ring, a, j, d);
    private static Formula OverRing(Formula body) => Seq(Bound("R", Named("Type")),
        Implication(Call("CommRing", F.Id("R")), body));

    private static Formula TailFormula()
    {
        var ring = F.Id("R");
        var a = F.Id("A");
        var j = F.Id("j");
        var d = F.Id("d");
        var square = Power(Call("cast", ring, Add(Mul(D(2), j), D(1))), D(2));
        return Disp(OverRing(Seq(Bound("A", Series(ring)), Bound("j", Naturals()),
            And(Equal(Tail(ring, a, j, D(0)), a),
                Seq(Bound("d", Naturals()), Equal(Tail(ring, a, j, Add(d, D(1))),
                    Subtract(a, Mul(Mul(Call("C", square), X()),
                        Inverse(Tail(ring, a, Add(j, D(1)), d))))))))));
    }

    private static Formula StableFormula()
    {
        var ring = F.Id("R");
        var a = F.Id("A");
        var j = F.Id("j");
        var d = F.Id("d");
        var e = F.Id("e");
        var n = F.Id("n");
        return Disp(OverRing(Seq(Bound("A", Series(ring)),
            Implication(Equal(Constant(a), D(1)), Seq(
                Bound("j", Naturals()), Bound("d", Naturals()), Bound("e", Naturals()), Bound("n", Naturals()),
                Implication(LessEqual(d, e), Implication(LessEqual(n, d),
                    Equal(Coeff(n, Tail(ring, a, j, d)), Coeff(n, Tail(ring, a, j, e))))))))));
    }

    private static Formula CoefficientFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var k = F.Id("k");
        return Disp(new Formula.Aligned([
            Seq(Bound("n", Naturals()), Equal(Call("a", n), Coeff(n, Call("P", n)))),
            Equal(Call("P", D(0)), D(1)),
            Seq(Bound("m", Naturals()), Bound("k", Naturals()),
                Equal(Coeff(k, Call("P", Add(m, D(1)))), Coeff(k,
                    Parenthesized(Add(D(1), Mul(X(), Inverse(Tail(Integers(), Call("P", m), D(1), k))))))))
        ]));
    }

    private static Formula SeriesFormula() => Disp(Equal(Generating(), Call("mk", Named("a"))));

    private static Formula FiniteEquation(Formula a)
    {
        var d = F.Id("d");
        var n = F.Id("n");
        return Seq(Bound("d", Naturals()), Bound("n", Naturals()),
            Implication(LessEqual(n, Add(d, D(1))), Equal(Coeff(n, D(1)),
                Coeff(n, Parenthesized(Subtract(a, Mul(X(), Inverse(Tail(Integers(), a, D(1), d)))))))));
    }

    private static Formula EquationFormula()
    {
        var j = F.Id("j");
        var d = F.Id("d");
        var tail = Tail(Integers(), Generating(), j, d);
        return Disp(And(Equal(Constant(Generating()), D(1)), And(
            Seq(Bound("j", Naturals()), Bound("d", Naturals()),
                And(Equal(Constant(tail), D(1)), Equal(Mul(tail, Inverse(tail)), D(1)))),
            FiniteEquation(Generating()))));
    }

    private static Formula UniqueFormula() => Disp(Seq(Bound("A", Series(Integers())),
        Implication(Equal(Constant(F.Id("A")), D(1)),
            Implication(FiniteEquation(F.Id("A")), Equal(F.Id("A"), Generating())))));

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Lt, Sp, F.Id("n")),
            Seq(D(8), Sp, Mid, Sp, Call("a", F.Id("n"))))));
}
