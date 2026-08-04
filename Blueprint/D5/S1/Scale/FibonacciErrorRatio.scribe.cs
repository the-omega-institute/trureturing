using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale;

internal sealed class FibonacciErrorRatioDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Scale/FibonacciErrorRatio",
                "Fibonacci convergents have an exact golden residual and a limiting error ratio."),
            H("Fibonacci Convergent Error Ratio"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("exact-signed-golden-residual"),
                    H("Exact signed golden residual"),
                    LeanTheorem(
                        "D5/S1/Scale/FibonacciErrorRatio.fibonacci_golden_residual"),
                    new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("N"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexSymbol(FormulaLatexSymbol.Minus), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([1])]), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexSymbol(FormulaLatexSymbol.Minus), new Formula.LatexMacro(FormulaLatexMacro.Left), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Minus), new Formula.LatexMacro(FormulaLatexMacro.Frac), new Formula.LatexGroup([new Formula.LatexDigits([1])]), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Varphi)]), new Formula.LatexMacro(FormulaLatexMacro.Right), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSymbol(FormulaLatexSymbol.Period)])),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For every natural index, multiplying the Fibonacci denominator by the "
                        + "golden ratio and subtracting the next Fibonacci number gives exactly "
                        + "the negative n-th power of the contracting factor -1/phi.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("adjacent-absolute-error-ratio"),
                    H("Adjacent absolute-error ratio"),
                    LeanTheorem(
                        "D5/S1/Scale/FibonacciErrorRatio.fibonacci_convergent_error_ratio"),
                    new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexWord(FormulaIdentifier.Create("e")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexSymbol(FormulaLatexSymbol.Minus), new Formula.LatexMacro(FormulaLatexMacro.Frac), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([2])])]), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([1])])]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.Quad), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Frac), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Lvert), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("e")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([1])]), new Formula.LatexMacro(FormulaLatexMacro.Rvert)]), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Lvert), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("e")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexMacro(FormulaLatexMacro.Rvert)]), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Frac), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([1])])]), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([2])])]), new Formula.LatexMacro(FormulaLatexMacro.Frac), new Formula.LatexGroup([new Formula.LatexDigits([1])]), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Varphi)]), new Formula.LatexSymbol(FormulaLatexSymbol.Period)])),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Let e_n be the signed error of the shifted Fibonacci convergent "
                        + "F_(n+2)/F_(n+1). Its adjacent absolute-error ratio is exactly the "
                        + "shifted ratio F_(n+1)/F_(n+2), divided by the golden ratio.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("absolute-error-ratio-limit"),
                    H("Limit of adjacent absolute-error ratios"),
                    LeanTheorem(
                        "D5/S1/Scale/FibonacciErrorRatio."
                        + "fibonacci_convergent_error_ratio_tendsto"),
                    new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Lim), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexMacro(FormulaLatexMacro.To), new Formula.LatexMacro(FormulaLatexMacro.Infty)]), new Formula.LatexMacro(FormulaLatexMacro.Frac), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Lvert), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("e")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([1])]), new Formula.LatexMacro(FormulaLatexMacro.Rvert)]), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Lvert), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("e")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexMacro(FormulaLatexMacro.Rvert)]), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Frac), new Formula.LatexGroup([new Formula.LatexDigits([1])]), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexDigits([2])]), new Formula.LatexSymbol(FormulaLatexSymbol.Period)])),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The adjacent absolute-error ratios of the shifted Fibonacci "
                        + "convergents tend to the reciprocal square of the golden ratio.")))
                ))));
}
