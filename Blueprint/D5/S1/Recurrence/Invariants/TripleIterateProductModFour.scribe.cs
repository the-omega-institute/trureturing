using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class TripleIterateProductModFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/TripleIterateProductModFour.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2026a396794");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every coefficient above degree one in OEIS A396794 is divisible by four.",
        H("Hanna's Triple-Iterate Product Congruence"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's OEIS A396794 entry states the generating "
                + "equation and divisibility conjecture recorded in hanna2026a396794. "
                + "The normalization is zero constant coefficient and coefficient one "
                + "at degree one. All series below have integer coefficients.")),
            Paragraph(Text("PowerSeries(Z) denotes the formal power-series ring, with "
                + "indeterminate X. The imported iterate(Z,f,3) is the third compositional "
                + "iterate f(f(f(X))); the powers of X and the displayed multiplication "
                + "are ordinary power-series operations. The operator choose selects a "
                + "witness of the displayed proved existential proposition. All coefficient "
                + "indices are natural numbers.")),
            Node("generatingSeries", "The normalized generating series", GeneratingFormula(),
                "Existence is proved by successive coefficient corrections, starting "
                + "from X. At degree n, the error coefficient at degree n+1 is divided "
                + "by four using integer division. The mod-sixteen product identity "
                + "makes this division exact and makes the correction divisible by four. "
                + "The stabilized coefficients give an integer series satisfying all "
                + "three clauses of the existential proposition.", DescribeRole.Definition),
            Node("a", "The coefficient sequence", CoefficientFormula(),
                "The value a(n) is the degree-n coefficient of generatingSeries. "
                + "The generating equation below gives a(0)=0 and a(1)=1.",
                DescribeRole.Definition),
            Node("generating_equation", "The OEIS equation and normalization", EquationFormula(),
                "The constructed series satisfies the product equation as an identity "
                + "of formal power series, together with both normalization conditions. "
                + "Existential witness selection preserves these three proved properties."),
            Node("generating_unique", "Uniqueness among normalized integer series", UniqueFormula(),
                "Suppose two normalized series agree below degree n. Their third "
                + "iterates differ at degree n by three times their coefficient difference. "
                + "Their products therefore differ at degree n+1 by four times that "
                + "difference. Equal products force equal coefficients, and strong "
                + "induction proves equality of the series."),
            Node("hanna_conjecture", "The A396794 divisibility conjecture", ConjectureFormula(),
                "Induct on n and truncate the solution below degree n. Earlier "
                + "coefficients make this prefix congruent to X modulo four. Over "
                + "ZMod(16), writing it as X+4B gives its jth iterate as X+4jB, "
                + "so its product with the third iterate is X squared. Comparing "
                + "the prefix with the solution by the coefficient-perturbation identity "
                + "gives 16 dividing 4a(n), hence 4 dividing a(n). This proves the "
                + "conjecture for every n greater than one.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396794-triple-iterate-product-mod-four"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a396794-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
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
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula Product(Formula f) => Mul(f, Call("iterate", Integers(), f, D(3)));
    private static Formula RightSide() => Add(Power(X(), D(2)), Mul(D(1, 6), Power(X(), D(3))));
    private static Formula NormalizedEquation(Formula f) => Seq(
        Parenthesized(Equal(Product(f), RightSide())), Sp, Land, Sp,
        Parenthesized(Seq(Parenthesized(Equal(Call("constantCoeff", f), D(0))), Sp, Land, Sp,
            Parenthesized(Equal(Call("coeff", D(1), f), D(1))))));

    private static Formula GeneratingFormula() => Disp(Equal(Generating(),
        Call("choose", Seq(Exists, Sp, F.Id("f"), Colon, Sp, Series(), Comma, Sp,
            Parenthesized(NormalizedEquation(F.Id("f")))))));

    private static Formula CoefficientFormula() => Disp(Seq(Bound("n", Naturals()),
        Equal(Call("a", F.Id("n")), Call("coeff", F.Id("n"), Generating()))));

    private static Formula EquationFormula() => Disp(NormalizedEquation(Generating()));

    private static Formula UniqueFormula() => Disp(Seq(Bound("f", Series()),
        Implication(Equal(Product(F.Id("f")), RightSide()),
            Implication(Equal(Call("constantCoeff", F.Id("f")), D(0)),
                Implication(Equal(Call("coeff", D(1), F.Id("f")), D(1)),
                    Equal(F.Id("f"), Generating()))))));

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Lt, Sp, F.Id("n")),
            Seq(D(4), Sp, Mid, Sp, Call("a", F.Id("n"))))));
}
