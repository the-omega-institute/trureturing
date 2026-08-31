using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class OddTestBudgetUpperBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A feasible finite odd test bounds the budget of a negative rank-one pencil from above.",
        H("Odd-Test Budget Upper Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("odd-test-budget-at-most-upper"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Budget/OddTestBudgetUpperBound."
                        + "odd_test_budget_at_most_upper"),
                H("One odd test requires a bounded budget"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite complex matrix, boundary vector, and selected odd test "
                            + "construct the negative rank-one pencil inequality directly.")),
                    Paragraph(Text(
                        "A nonzero boundary pairing makes its norm square positive. Dividing "
                            + "the pencil inequality by that quantity gives the displayed "
                            + "test-specific Rayleigh upper bound.")),
                    Paragraph(Text(
                        "Repository, pinned-library, and public Lean searches found no exact "
                            + "budget theorem; the proof applies the pinned norm-square and "
                            + "positive-division lemmas."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula count = F.Id("n");
        Formula baseMatrix = F.Id("B");
        Formula boundary = F.Id("s");
        Formula test = F.Id("o");
        Formula reference = F.Id("R0");
        Formula budget = F.Id("R");
        Formula finCount = Call("Fin", count);
        Formula vector = Seq(finCount, Sp, To, Sp, complex);
        Formula matrix = Call("Matrix", finCount, finCount, complex);
        Formula boundaryPairing = Overlap(boundary, test);
        Formula boundarySquare = Call("normSq", boundaryPairing);
        Formula quadratic = Call(
            "Re", Overlap(test, Call("mulVec", baseMatrix, test)));
        Formula shiftedBudget = Seq(
            Open, budget, Sp, Minus, Sp, reference, Close,
            Sp, Cdot, Sp, boundarySquare);
        Formula pencilValue = Seq(
            quadratic, Sp, Minus, Sp, shiftedBudget);
        Formula upper = Seq(
            reference, Sp, Plus, Sp,
            new Formula.Fraction(quadratic, boundarySquare));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, count, Colon, Sp, natural, Comma,
            RowBreak, Grp(),
            baseMatrix, Colon, Sp, matrix, Comma,
            RowBreak, Grp(),
            boundary, Comma, Sp, test, Colon, Sp, vector, Comma,
            RowBreak, Grp(),
            reference, Comma, Sp, budget, Colon, Sp, real, Comma,
            RowBreak, Grp(),
            boundaryPairing, Sp, Neq, Sp, D(0), Sp, Land,
            RowBreak, Grp(),
            D(0), Sp, Le, Sp, pencilValue, Sp, Rightarrow,
            RowBreak, Grp(),
            budget, Sp, Le, Sp, upper, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Overlap(Formula left, Formula right) =>
        Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
