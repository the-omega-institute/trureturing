using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class MaxDigitSumBaseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/MaxDigitSumBase.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/irvine2026a394431");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Past eight, the least base maximizing the digit sum of a number is the first base above "
            + "half of it, because every base at most half loses more than half of the number to "
            + "carries while the first base above half keeps all but half.",
        H("The Least Base Maximizing the Digit Sum Is the First Base Above Half"),
        Blocks(
            Node("digit-sum", "Digit sum in a base", "digitSum", DigitSumFormula(),
                "The digit sum of a natural number in a base is the sum of the list of its digits "
                    + "in that base, least significant first. The number zero has the empty list "
                    + "and so digit sum zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("least-maximizing-base", "Least base maximizing the digit sum",
                "IsLeastMaxDigitSumBase", LeastBaseFormula(),
                "A base is the least maximizing base of a number when it lies strictly between one "
                    + "and the number, no base in that range gives a larger digit sum, and every "
                    + "smaller base in that range gives a strictly smaller one. This is the value "
                    + "the source entry records for every number above two.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("the-conjecture", "The conjecture", "claim", ClaimFormula(),
                "The source asserts that for every number above eight the least maximizing base is "
                    + "the ceiling of half of the number plus one. At eight the assertion fails, "
                    + "since bases three and five both give digit sum four.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("the-conjecture-holds", "The conjecture holds", "result", ResultFormula(),
                "The ceiling of half of the number plus one is the least base exceeding half of the "
                    + "number. For a base above half and below the number, the number has exactly "
                    + "two digits, one and the number minus the base, so its digit sum is the number "
                    + "minus the base plus one; this is largest at the least such base, where it "
                    + "equals the number minus its floor half. For a base at most half, write the "
                    + "number as the base times a quotient of at least two plus a remainder below "
                    + "the base, so the digit sum is the remainder plus the digit sum of the "
                    + "quotient. A digit sum never exceeds its argument, and when the quotient is at "
                    + "least the base, one more expansion shows that its digit sum is smaller by at "
                    + "least the base minus one. When the quotient is below the base, the base is at "
                    + "least four, since bases two and three with such a quotient force the number "
                    + "to be at most eight. In either case twice the digit sum is below the number, "
                    + "hence below the value at the first base above half. The only case of "
                    + "equality in these bounds is base three with quotient and remainder two, the "
                    + "number eight that the conjecture excludes.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("irvine-least-maximal-digit-sum-base"),
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

    private static Formula S(Formula b, Formula n) =>
        Seq(F.Id("s"), Underscore, Grp(b), Open, n, Close);

    private static Formula DigitSumFormula() =>
        Disp(Equal(S(F.Id("b"), F.Id("n")),
            Seq(Sum, Underscore, Grp(Seq(F.Id("d"), InMacro, Sp,
                Operatorname, Grp(F.Id("digits")), Open, F.Id("b"), Comma, Sp, F.Id("n"), Close)),
                Sp, F.Id("d"))));

    private static Formula L(Formula n, Formula b) =>
        Seq(F.Id("L"), Open, n, Comma, Sp, b, Close);

    private static Formula LeastBaseFormula() =>
        Disp(Iff(L(F.Id("n"), F.Id("b")),
            Seq(D(1), Lt, F.Id("b"), Lt, F.Id("n"), Sp, Land, Sp,
                Forall, Sp, F.Id("c"), Comma, Sp,
                Grp(Seq(D(1), Lt, F.Id("c"), Lt, F.Id("n"), Sp, Rightarrow, Sp,
                    S(F.Id("c"), F.Id("n")), Leq, S(F.Id("b"), F.Id("n")))),
                Sp, Land, Sp, Forall, Sp, F.Id("c"), Comma, Sp,
                Grp(Seq(D(1), Lt, F.Id("c"), Lt, F.Id("b"), Sp, Rightarrow, Sp,
                    S(F.Id("c"), F.Id("n")), Lt, S(F.Id("b"), F.Id("n")))))));

    private static Formula Ceiling() =>
        Seq(Operatorname, Grp(F.Id("ceil")), Open,
            Frac, Grp(Seq(F.Id("n"), Plus, D(1))), Grp(D(2)), Close);

    private static Formula Statement() =>
        Seq(Forall, Sp, F.Id("n"), Comma, Sp,
            Implication(Seq(D(8), Lt, F.Id("n")), L(F.Id("n"), Ceiling())));

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
