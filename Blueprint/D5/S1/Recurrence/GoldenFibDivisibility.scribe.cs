using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class GoldenFibDivisibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Recurrence/GoldenFibDivisibility",
            "Fibonacci divisibility detects divisibility of indices from index three onward."),
        H("Fibonacci Divisibility and Indices"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("fibonacci-divisibility-detects-index-divisibility"),
                H("Fibonacci divisibility detects index divisibility"),
                LeanTheorem(
                    "D5/S1/Recurrence/GoldenFibDivisibility.fib_dvd_iff"),
                new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Ge), new Formula.LatexSpace(), new Formula.LatexDigits([3]), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Implies), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Left), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Mid), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexWord(FormulaIdentifier.Create("b")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Iff), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Mid), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("b")), new Formula.LatexMacro(FormulaLatexMacro.Right), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis)])),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For natural indices a and b with a at least three, the Fibonacci "
                    + "number F_a divides F_b exactly when a divides b. The lower bound "
                    + "removes the exceptional index two, where F_2 equals one.")))))));
}
