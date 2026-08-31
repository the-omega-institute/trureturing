using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class OddTestBudgetUpperBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The admissible finite odd-test family bounds a negative rank-one pencil's budget "
            + "by its Rayleigh-infimum endpoint.",
        H("Odd-Test Family Budget Upper Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("odd-test-budget-at-most-upper"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Budget/OddTestBudgetUpperBound."
                        + "odd_test_budget_at_most_upper"),
                H("The odd-test family bounds the budget by its infimum endpoint"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The public odd-test quotient set contains the Rayleigh quotient of "
                            + "every finite complex test with nonzero boundary pairing. Its "
                            + "upper endpoint is the reference budget plus the real infimum of "
                            + "that entire set.")),
                    Paragraph(Text(
                        "The family is explicitly nonempty and bounded below. Nonnegativity of "
                            + "the negative rank-one pencil is assumed for every admissible test; "
                            + "each nonzero boundary pairing has positive norm square, so division "
                            + "makes the shifted budget a lower bound of every quotient. The "
                            + "conditional infimum property then gives the endpoint bound.")),
                    Paragraph(Text(
                        "The repository contains a generic parity endpoint construction, but no "
                            + "finite-matrix theorem exposing this negative rank-one pencil. The "
                            + "proof reuses the pinned norm-square, positive-division, and real "
                            + "infimum lemmas."))),
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
        Formula quotient = F.Id("q");
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
        Formula rayleigh = new Formula.Fraction(quadratic, boundarySquare);
        Formula quotientPredicate = Seq(
            Exists, Sp, test, Colon, Sp, vector, Comma, Sp,
            boundaryPairing, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            quotient, Sp, Eq, Sp, rayleigh);
        Formula quotientSet = new Formula.SetBuilder(
            quotientPredicate, quotient, real);
        Formula admissibleFamilyNonempty = Seq(
            Exists, Sp, test, Colon, Sp, vector, Comma, Sp,
            boundaryPairing, Sp, Neq, Sp, D(0));
        Formula universalPencil = Seq(
            Forall, Sp, test, Colon, Sp, vector, Comma, Sp,
            boundaryPairing, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            D(0), Sp, Le, Sp, pencilValue);
        Formula upper = Seq(reference, Sp, Plus, Sp, Call("sInf", quotientSet));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, count, Colon, Sp, natural, Comma,
            RowBreak, Grp(),
            baseMatrix, Colon, Sp, matrix, Comma,
            RowBreak, Grp(),
            boundary, Colon, Sp, vector, Comma,
            RowBreak, Grp(),
            reference, Comma, Sp, budget, Colon, Sp, real, Comma,
            RowBreak, Grp(),
            Open, Open, admissibleFamilyNonempty, Close, Sp, Land,
            RowBreak, Grp(),
            Call("BddBelow", quotientSet), Sp, Land,
            RowBreak, Grp(),
            Open, universalPencil, Close, Close, Sp, Rightarrow,
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
