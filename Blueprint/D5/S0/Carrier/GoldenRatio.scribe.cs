using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class GoldenRatioDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Carrier/GoldenRatio",
            "The real golden ratio satisfies its radical, fixed-point, and conjugate identities."),
        H("Golden Ratio Identities"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("radical-fixed-point-and-conjugate-identities"),
                H("Radical, fixed-point, and conjugate identities"),
                LeanTheorem(
                    "D5/S0/Carrier/GoldenRatio.golden_ratio_spec"),
                new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Frac), new Formula.LatexGroup([new Formula.LatexDigits([1]), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Sqrt), new Formula.LatexGroup([new Formula.LatexDigits([5])])]), new Formula.LatexGroup([new Formula.LatexDigits([2])]), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Land), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexGroup([new Formula.LatexDigits([2])]), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexSpace(), new Formula.LatexDigits([1]), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Land), new Formula.LatexSpace(), new Formula.LatexDigits([1]), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.Minus), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.Minus), new Formula.LatexMacro(FormulaLatexMacro.Frac), new Formula.LatexGroup([new Formula.LatexDigits([1])]), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Varphi)])])),
                DescribeProvenance.LiteratureAttested(
                    LibraryNoteRef.Create("D5/L/koshy2001fibonacci")),
                Blocks(Paragraph(Text(
                    "One kernel-checked conjunction records the radical definition, the quadratic fixed point, and the negative-reciprocal conjugate identity.")))
            ))));
}
