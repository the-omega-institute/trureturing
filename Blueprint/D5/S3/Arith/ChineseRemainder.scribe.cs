using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class ChineseRemainderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Arith/ChineseRemainder",
            "The natural map modulo coprime factors is bijective."),
        H("Chinese Remainder Bijectivity"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-natural-map-modulo-coprime-factors-is-bijective"),
                H("The natural map modulo coprime factors is bijective"),
                LeanTheorem(
                    "D5/S3/Arith/ChineseRemainder.chinese_remainder_bijective"),
                new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Gcd), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("m")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexDigits([1]), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Rightarrow), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Left), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Z"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Slash), new Formula.LatexWord(FormulaIdentifier.Create("mn")), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Z"))]), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.To), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Z"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Slash), new Formula.LatexWord(FormulaIdentifier.Create("m")), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Z"))]), new Formula.LatexMacro(FormulaLatexMacro.Times), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Z"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Slash), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Z"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexMacro(FormulaLatexMacro.Mapsto), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("mod"))]), new Formula.LatexWord(FormulaIdentifier.Create("m")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("mod"))]), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Right), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Text), new Formula.LatexGroup([new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("is")), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("bijective"))])])),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For coprime natural numbers m and n, the theorem fixes the natural map "
                        + "from integers modulo m times n to the product of the residue rings "
                        + "modulo m and modulo n. Its two readings are the canonical casts to "
                        + "the factor moduli. The conclusion states that this displayed map is "
                        + "bijective, rather than merely asserting that some bijection between "
                        + "the two finite carriers exists.")),
                    Paragraph(Text(
                        "The atom's proof skeleton establishes injectivity from coprimality and "
                        + "then obtains surjectivity by counting the two finite carriers. The "
                        + "formal proof uses Mathlib's ZMod.chineseRemainder ring equivalence, "
                        + "whose forward function is definitionally the same ZMod.castHom natural "
                        + "map displayed in the statement, and assembles the result through the "
                        + "equivalence's bijectivity. This is a faithful library-level assembly of "
                        + "the atomic skeleton under precedent 6.1, and it asserts no numerical "
                        + "certificate.")))
            ))));
}
