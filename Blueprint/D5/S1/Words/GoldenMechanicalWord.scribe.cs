using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class GoldenMechanicalWordDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Words/GoldenMechanicalWord",
                "Identify the exact fractional-coordinate window for a golden mechanical letter."),
            H("Golden Mechanical Word Window"),
            Blocks(
                Paragraph(Text(
                    "The lower golden mechanical word is defined by consecutive floor differences at slope one over the golden ratio. The theorem below gives an exact local test using the existing golden fractional coordinate.")),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("golden-mechanical-letter-window"),
                    H("A letter is one exactly on the local window"),
                    LeanTheorem(
                        "D5/S1/Words/GoldenMechanicalWord.golden_mechanical_letter_eq_one_iff"),
                    new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("N"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexDigits([1]), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Leftrightarrow), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.OpenBrace), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexMacro(FormulaLatexMacro.CloseBrace), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexSymbol(FormulaLatexSymbol.OpenBracket), new Formula.LatexDigits([1]), new Formula.LatexSymbol(FormulaLatexSymbol.Minus), new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexGroup([new Formula.LatexSymbol(FormulaLatexSymbol.Minus), new Formula.LatexDigits([1])]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexDigits([1]), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis)])),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For every natural index, the floor-difference letter equals one if and only if the golden fractional coordinate lies in the stated half-open interval. No complexity, substitution, or cut-and-project classification is asserted.")))
                ))));
}
