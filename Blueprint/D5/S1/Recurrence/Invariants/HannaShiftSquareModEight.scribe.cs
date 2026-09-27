using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class HannaShiftSquareModEightDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/HannaShiftSquareModEight.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a392203");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Modulo eight the series fixed by substituting the variable minus itself is the rational "
            + "function with coefficients one at even and three at odd degrees, because that function "
            + "satisfies the equation modulo eight and the equation has only one solution.",
        H("Hanna's Shift-Square Series Is Rational Modulo Eight"),
        Blocks(
            Node("solution", "Solutions of the equation", "IsSolution", SolutionFormula(),
                "An integer power series is a solution when its constant and linear coefficients "
                    + "vanish and substituting the variable minus the series into it gives the square "
                    + "of the variable plus the variable times the series.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("the-conjecture", "The conjecture", "claim", ClaimFormula(),
                "The source observes that the coefficients at even indices from two on are one and "
                    + "those at odd indices from three on are three, modulo eight. The proposition "
                    + "also asserts that a solution exists, so that the universal part is not vacuous.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("the-conjecture-holds", "The conjecture holds", "result", ResultFormula(),
                "Consider the map sending a series to the square of the variable, plus the variable "
                    + "times the series, minus the difference between the series evaluated at the "
                    + "variable minus the series and the series itself; solutions are its fixed "
                    + "points. For two series of order at least two agreeing below some degree, their "
                    + "images agree one degree further: multiplying by the variable raises the order, "
                    + "each power of the substituted argument of exponent at least two changes by a "
                    + "multiple of the difference times a series without constant term, and the "
                    + "leading term of the difference cancels against itself after substitution. "
                    + "Iterating the map from zero over the integers therefore stabilises each "
                    + "coefficient, and the stabilised series is a solution. Over the integers modulo "
                    + "eight the same estimate makes the solution unique. The series with "
                    + "coefficients one at even and three at odd degrees from two on equals the "
                    + "square of the variable plus three times its cube, divided by one minus the "
                    + "square of the variable; clearing these denominators turns the equation for it "
                    + "into a polynomial identity whose two integer sides differ by a multiple of "
                    + "eight, and the cleared factors have constant term one, so this series is the "
                    + "solution modulo eight. Reducing any integer solution modulo eight therefore "
                    + "gives it, which is the source's observation.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hanna-shift-square-mod-eight"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula Series() =>
        Seq(Mathbb, Grp(F.Id("Z")), OpenBracket, OpenBracket, F.Id("X"), CloseBracket, CloseBracket);

    private static Formula Sol(Formula a) =>
        Seq(Operatorname, Grp(F.Id("IsSolution")), Open, a, Close);

    private static Formula Coeff(Formula index) =>
        Seq(Operatorname, Grp(F.Id("coeff")), Open, index, Comma, Sp, F.Id("A"), Close);

    private static Formula SolutionFormula() =>
        Disp(Seq(Forall, Sp, F.Id("A"), InMacro, Sp, Series(), Comma, Sp,
            Iff(Sol(F.Id("A")),
                Seq(Operatorname, Grp(F.Id("constantCoeff")), Open, F.Id("A"), Close, Eq, D(0), Sp, Land, Sp, Coeff(D(1)), Eq, D(0), Sp, Land, Sp,
                    F.Id("A"), Sp, Circ, Sp, Open, F.Id("X"), Minus, F.Id("A"), Close, Eq,
                    F.Id("X"), Caret, Grp(D(2)), Plus, F.Id("X"), Sp, Cdot, Sp, F.Id("A")))));

    private static Formula Statement() =>
        Seq(Open, Exists, Sp, F.Id("A"), InMacro, Sp, Series(), Comma, Sp, Sol(F.Id("A")), Close,
            Sp, Land, Sp,
            Open, Forall, Sp, F.Id("A"), InMacro, Sp, Series(), Comma, Sp,
            Implication(Sol(F.Id("A")),
                Seq(Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Implication(Seq(D(1), Leq, Sp, F.Id("n")),
                        Seq(Coeff(Seq(D(2), F.Id("n"))), Sp, Operatorname, Grp(F.Id("mod")), Sp, D(8),
                            Eq, D(1), Sp, Land, Sp,
                            Coeff(Seq(D(2), F.Id("n"), Plus, D(1))), Sp, Operatorname, Grp(F.Id("mod")),
                            Sp, D(8), Eq, D(3))))),
            Close);

    private static Formula ClaimFormula() => Disp(Iff(F.Id("claim"), Statement()));

    private static Formula ResultFormula() => Disp(Statement());

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
