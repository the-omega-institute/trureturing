using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class TrinomialOddDiagonalRationalSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Analytic/schulte2015a077864");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schulte's conjectured odd diagonal equals the coefficients of a rational power series.",
        H("The Trinomial Odd Diagonal of OEIS A077864"),
        Blocks(
            Paragraph(Text(
                "OEIS A077864 is the expansion of (1-x)^(-1)/(1-x-2*x^2-x^3). "
                    + "Its FORMULA section records Deléham's order-four recurrence and "
                    + "Schulte's conjecture identifying its coefficients with an odd "
                    + "diagonal of the trinomial triangle A027907.")),
            Paragraph(Text(
                "All indices are natural numbers. The trinomial value is the coefficient "
                    + "of X^r in (1+X+X^2)^m. The diagonal sum uses n/2 as integer division. "
                    + "The power series and its coefficient function take values in the "
                    + "rationals; coeff extracts a degree and inv denotes a power-series "
                    + "inverse. The operator expand 2 selects even powers and rescale(-1) "
                    + "reverses the sign of odd coefficients.")),
            Node("trinomial", "The trinomial coefficient", TrinomialFormula(),
                "This is the coefficient definition of the rows of A027907.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("generatingSeries", "The rational generating series",
                GeneratingSeriesFormula(),
                "This rational power series is the expansion named in A077864, with "
                    + "coefficients in the rationals.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "The coefficient sequence", AFormula(),
                "The value a(n) is the degree-n coefficient of the rational generating "
                    + "series, so it is rational-valued in this formalization.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("odd_trinomial_diagonal_coeff", "The odd coefficient identity",
                OddTrinomialFormula(),
                "Substituted geometric powers have finite support at every fixed degree. "
                    + "Reflection of the finite sum and the polynomial degree tail bound "
                    + "give the displayed odd diagonal coefficient identity.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("schulte_a077864", "Schulte's A077864 conjecture",
                SchulteFormula(),
                "The two reflected inverse equations and their denominator product give "
                    + "the odd-part identity 2·X^3·(expand 2 G') = G - rescale(-1) G. "
                    + "Coefficient extraction reduces it to the preceding odd diagonal "
                    + "identity.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a077864-trinomial-odd-diagonal-rational-series"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a077864-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula N() => F.Id("n");
    private static Formula M() => F.Id("m");
    private static Formula R() => F.Id("r");
    private static Formula J() => F.Id("j");
    private static Formula X() => F.Id("X");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Sp, InMacro, Sp, type, Comma, Sp);
    private static Formula Coefficient(Formula index, Formula series) =>
        Call("coeff", index, series);
    private static Formula Trinomial(Formula row, Formula index) =>
        Call("trinomial", row, index);
    private static Formula Sum(Formula n) => Seq(
        new Formula.Subscript(F.Sum, Seq(J(), Sp, InMacro, Sp,
            Call("range", Add(Call("div", n, D(2)), D(1))))),
        Sp, Parenthesized(Trinomial(
            Subtract(Add(n, D(1)), J()), Add(Multiply(D(2), J()), D(1)))));

    private static Formula TrinomialFormula() => Disp(Seq(
        Bound("m", Naturals()), Bound("r", Naturals()),
        Equal(Trinomial(M(), R()), Call("coeff", Power(
            Add(Add(D(1), X()), Power(X(), D(2))), M()), R()))));

    private static Formula GeneratingSeriesFormula()
    {
        Formula first = Call("inv", Parenthesized(Subtract(D(1), X())));
        Formula second = Call("inv", Parenthesized(Subtract(
            Subtract(Subtract(D(1), X()), Multiply(D(2), Power(X(), D(2)))),
            Power(X(), D(3)))));
        return Disp(Equal(Named("generatingSeries"), Multiply(first, second)));
    }

    private static Formula AFormula() => Disp(Seq(
        Bound("n", Naturals()), Equal(Call("a", N()),
            Coefficient(N(), Named("generatingSeries")))));

    private static Formula OddTrinomialFormula()
    {
        Formula polynomial = Add(Add(D(1), X()), Power(X(), D(2)));
        Formula denominator = Subtract(D(1), Multiply(Power(X(), D(2)),
            Parenthesized(polynomial)));
        return Disp(Seq(Bound("n", Naturals()), Equal(
            Coefficient(Add(Multiply(D(2), N()), D(3)),
                Call("inv", Parenthesized(denominator))), Sum(N()))));
    }

    private static Formula SchulteFormula() => Disp(Seq(
        Bound("n", Naturals()), Equal(Call("a", N()), Sum(N()))));
}
