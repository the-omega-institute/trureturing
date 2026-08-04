using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class QuadraticResiduesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/PrimeForms/QuadraticResidues",
            "Squares occupy only residues zero and one modulo four, obstructing residue three."),
        H("Quadratic Residues Modulo Four"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("square-residues-and-sum-obstruction"),
                H("Square residues and the two-square obstruction"),
                LeanTheorem(
                    "D5/S3/PrimeForms/QuadraticResidues."
                    + "square_residues_and_sum_obstruction"),
                new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Left), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("N"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexDigits([2]), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("mod"))]), new Formula.LatexDigits([4]), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.OpenBrace), new Formula.LatexDigits([0]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexDigits([1]), new Formula.LatexMacro(FormulaLatexMacro.CloseBrace), new Formula.LatexMacro(FormulaLatexMacro.Right), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Land), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Left), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("b")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("N"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexDigits([2]), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexWord(FormulaIdentifier.Create("b")), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexDigits([2]), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("mod"))]), new Formula.LatexDigits([4]), new Formula.LatexMacro(FormulaLatexMacro.Neq), new Formula.LatexDigits([3]), new Formula.LatexMacro(FormulaLatexMacro.Right), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Period)])),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Every natural square has residue zero or one modulo four. Consequently, "
                        + "the sum of two natural squares cannot have residue three modulo four.")),
                    Paragraph(Text(
                        "Methodologically, the zeroth-layer refutation certificate is the R_4 "
                        + "reading: inspect the square image {0, 1}, then its pairwise-sum image "
                        + "{0, 1, 2}. This certificate explains the proof search but is not an "
                        + "additional clause of the formal theorem.")))
            ))));
}
