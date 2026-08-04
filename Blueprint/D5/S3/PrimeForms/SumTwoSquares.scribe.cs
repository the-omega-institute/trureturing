using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class SumTwoSquaresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/PrimeForms/SumTwoSquares",
            "A prime congruent to one modulo four is a sum of two natural squares."),
        H("Prime Representation as a Sum of Two Squares"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("prime-congruent-to-one-is-a-sum-of-two-squares"),
                H("A prime congruent to one modulo four is a sum of two squares"),
                LeanTheorem(
                    "D5/S3/PrimeForms/SumTwoSquares."
                    + "prime_eq_sq_add_sq_of_mod_four_eq_one"),
                new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexWord(FormulaIdentifier.Create("p")), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Text), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("prime"))]), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Land), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexWord(FormulaIdentifier.Create("p")), new Formula.LatexMacro(FormulaLatexMacro.Equiv), new Formula.LatexSpace(), new Formula.LatexDigits([1]), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("mod"))]), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexDigits([4]), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Quad), new Formula.LatexMacro(FormulaLatexMacro.Rightarrow), new Formula.LatexMacro(FormulaLatexMacro.Quad), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Exists), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("b")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("N"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexWord(FormulaIdentifier.Create("p")), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexDigits([2]), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexWord(FormulaIdentifier.Create("b")), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexDigits([2])])),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For every natural prime p whose remainder modulo four is one, there are "
                    + "natural numbers a and b such that p equals a squared plus b squared. "
                    + "The formal statement retains both the primality and congruence premises "
                    + "and asserts only existence, without adding positivity or uniqueness of "
                    + "the witnesses. The proof installs the explicit primality hypothesis as "
                    + "the local fact required by Mathlib, specializes the standard sum-of-two-"
                    + "squares result after excluding remainder three, and reverses its final "
                    + "equality. No numerical certificate is asserted.")))
            ))));
}
