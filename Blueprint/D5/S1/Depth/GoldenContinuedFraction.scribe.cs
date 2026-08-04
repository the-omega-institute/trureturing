using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth;

internal sealed class GoldenContinuedFractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Depth/GoldenContinuedFraction",
            "The continued fraction of the golden ratio has constant unit coefficients."),
        H("The Golden Continued Fraction"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("golden-ratio-continued-fraction"),
                H("Every continued-fraction coefficient is one"),
                LeanTheorem(
                    "D5/S1/Depth/GoldenContinuedFraction.golden_ratio_continued_fraction"),
                new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.OpenBracket), new Formula.LatexMacro(FormulaLatexMacro.ThinSpace), new Formula.LatexDigits([1]), new Formula.LatexSymbol(FormulaLatexSymbol.Semicolon), new Formula.LatexMacro(FormulaLatexMacro.Overline), new Formula.LatexGroup([new Formula.LatexDigits([1])]), new Formula.LatexMacro(FormulaLatexMacro.ThinSpace), new Formula.LatexSymbol(FormulaLatexSymbol.CloseBracket)])),                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Mathlib's generalized continued fraction of the real golden ratio "
                    + "has head one, and every subsequent numerator-denominator pair is "
                    + "the pair (1, 1).")))))));
}
