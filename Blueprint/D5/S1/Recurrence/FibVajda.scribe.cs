using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FibVajdaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Recurrence/FibVajda",
            "Vajda's identity relates shifted Fibonacci products over the integers."),
        H("Vajda's Fibonacci Identity"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("vajda-fibonacci-identity"),
                H("Vajda's identity"),
                LeanTheorem(
                    "D5/S1/Recurrence/FibVajda.fib_vajda"),
                new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexWord(FormulaIdentifier.Create("i"))]), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexWord(FormulaIdentifier.Create("j"))]), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.Minus), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexWord(FormulaIdentifier.Create("i")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexWord(FormulaIdentifier.Create("j"))]), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Minus), new Formula.LatexDigits([1]), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexWord(FormulaIdentifier.Create("i")), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexWord(FormulaIdentifier.Create("j"))])),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For natural indices n, i, and j, the difference between the two "
                    + "shifted Fibonacci products F_(n+i)F_(n+j) and F_nF_(n+i+j) equals "
                    + "(-1)^n F_iF_j. All terms are interpreted in the integers.")))))));
}
