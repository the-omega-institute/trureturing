using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class PrimeAxisAdditionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Digit/PrimeAxisAddition",
            "Rowwise W normalization of prime-axis table sums decodes as multiplication."),
        H("Prime-Axis Normalized Addition"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("prime-axis-rowwise-normalization-product"),
                H("Rowwise normalized addition and decoder multiplication"),
                LeanTheorem(
                    "D5/S1/Digit/PrimeAxisAddition.prime_axis_addition_spec"),
                new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("z")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("w")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("PrimeAxisTable"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Bijective"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("primeAxisEncoding"))]), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Land), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("decodePrimeAxisTable"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("normalizedPrimeAxisAdd"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("z")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("w")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("decodePrimeAxisTable"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("z")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("decodePrimeAxisTable"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("w")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis)])),                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Prime-indexed canonical W rows are equivalent to positive naturals. Adding raw rows and applying the existing local W normalizer preserves exponent sums, so the finite prime-power decoder turns the normalized table sum into multiplication.")))
            ))));
}
