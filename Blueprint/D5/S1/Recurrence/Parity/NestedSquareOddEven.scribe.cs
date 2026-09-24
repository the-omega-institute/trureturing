using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Parity;

internal sealed class NestedSquareOddEvenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Parity/NestedSquareOddEven.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a392210");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A series equal to x plus a square has even coefficients at every odd index above one, "
            + "because the square pairs each term of an odd coefficient with its mirror image.",
        H("The Nested-Square Generating Function Has Even Odd-Index Coefficients"),
        Blocks(
            Node("shift", "The substitution x over one minus x", "shift", ShiftFormula(),
                "The substituted series is the variable times the series all of whose coefficients "
                    + "are one, which is the inverse of one minus the variable. Its constant "
                    + "coefficient is zero, so substituting it into an integer power series is "
                    + "well defined.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("functional-equation", "The functional equation", "IsNestedSquareGF",
                EquationFormula(),
                "An integer power series satisfies the equation when it equals the variable plus "
                    + "the square of the series obtained by substituting the shift into it. "
                    + "Iterating the equation at the shifted argument reproduces the infinitely "
                    + "nested square of the source entry, since substituting the variable over one "
                    + "minus the variable into the variable over one minus k times the variable "
                    + "gives the variable over one minus k plus one times the variable.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("the-conjecture", "The conjecture", "claim", ClaimFormula(),
                "The source observes that the coefficients at the odd indices two n minus one are "
                    + "even for every n above one. The proposition also asserts that the equation "
                    + "has a solution, so that the universal part is not vacuous.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("the-conjecture-holds", "The conjecture holds", "result", ResultFormula(),
                "A solution is built from the source's coefficient recurrence, in which each "
                    + "coefficient is the self-convolution of the binomial transform of the earlier "
                    + "ones: the power of the shift with exponent k has coefficient the binomial "
                    + "coefficient of m minus one over k minus one at degree m, so substituting the "
                    + "shift sends a coefficient sequence to its binomial transform, and comparing "
                    + "coefficients gives the equation. For any solution and any index two m plus "
                    + "one with m at least one, the variable contributes nothing, and the "
                    + "coefficient of the square is the sum over the pairs of indices adding to two "
                    + "m plus one. Reflecting the upper half of that range onto the lower half shows "
                    + "the sum to be twice the sum over the lower half, since an odd total admits no "
                    + "pair of equal indices.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hanna-nested-square-odd-coefficients"),
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

    private static Formula ShiftFormula() =>
        Disp(Equal(F.Id("g"),
            Seq(F.Id("X"), Sp, Cdot, Sp, Sum, Underscore, Grp(Seq(F.Id("k"), Geq, Sp, D(0))), Sp,
                F.Id("X"), Caret, Grp(F.Id("k")))));

    private static Formula Gf(Formula a) =>
        Seq(Operatorname, Grp(F.Id("IsNestedSquareGF")), Open, a, Close);

    private static Formula EquationFormula() =>
        Disp(Seq(Forall, Sp, F.Id("A"), InMacro, Sp, Mathbb, Grp(F.Id("Z")), OpenBracket, OpenBracket,
            F.Id("X"), CloseBracket, CloseBracket, Comma, Sp,
            Iff(Gf(F.Id("A")),
                Equal(F.Id("A"),
                    Seq(F.Id("X"), Plus, Open, F.Id("A"), Sp, Circ, Sp, F.Id("g"), Close, Caret,
                        Grp(D(2)))))));

    private static Formula Series() =>
        Seq(Mathbb, Grp(F.Id("Z")), OpenBracket, OpenBracket, F.Id("X"), CloseBracket, CloseBracket);

    private static Formula Coeff(Formula index) =>
        Seq(Operatorname, Grp(F.Id("coeff")), Open, index, Comma, Sp, F.Id("A"), Close);

    private static Formula Statement() =>
        Seq(Open, Exists, Sp, F.Id("A"), InMacro, Sp, Series(), Comma, Sp, Gf(F.Id("A")), Close,
            Sp, Land, Sp,
            Open, Forall, Sp, F.Id("A"), InMacro, Sp, Series(), Comma, Sp,
            Implication(Gf(F.Id("A")),
                Seq(Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Implication(Seq(D(1), Lt, F.Id("n")),
                        Seq(Operatorname, Grp(F.Id("Even")), Open,
                            Coeff(Seq(D(2), F.Id("n"), Minus, D(1))), Close)))),
            Close);

    private static Formula ClaimFormula() => Disp(Iff(F.Id("claim"), Statement()));

    private static Formula ResultFormula() => Disp(Statement());

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}
