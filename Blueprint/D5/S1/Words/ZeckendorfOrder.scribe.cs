using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words;

internal sealed class ZeckendorfOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Words/ZeckendorfOrder",
            "Greatest-index-first Zeckendorf representations carry numerical order lexicographically."),
        H("Order on Zeckendorf Representations"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("zeckendorf-lexicographic-order-matches-fibonacci-sums"),
                H("Lexicographic order matches Fibonacci sums"),
                LeanTheorem(
                    "D5/S1/Words/ZeckendorfOrder.isZeckendorfRep_lex_iff_sum_fib_lt"),
                new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("IsZeck"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("l")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Land), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("IsZeck"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Implies), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Left), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("l")), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.LessThan), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Text), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("lex"))])]), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Iff), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Sum), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("i")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("l"))]), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexWord(FormulaIdentifier.Create("i")), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.LessThan), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Sum), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("j")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("k"))]), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexWord(FormulaIdentifier.Create("j")), new Formula.LatexMacro(FormulaLatexMacro.Right), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis)])),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For two valid Zeckendorf index lists ordered from greatest index "
                    + "downward, strict lexicographic order is equivalent to strict order "
                    + "of the corresponding sums of Fibonacci numbers.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("canonical-zeckendorf-order-embedding"),
                H("Canonical Zeckendorf representations preserve strict order"),
                LeanTheorem(
                    "D5/S1/Words/ZeckendorfOrder.zeckendorf_lex_iff_lt"),
                new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("zeck"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("m")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.LessThan), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Text), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("lex"))])]), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("zeck"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Iff), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("m")), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.LessThan), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("n"))])),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Mathlib's canonical Zeckendorf representation maps natural numbers "
                    + "to greatest-index-first lists so that list lexicographic order holds "
                    + "exactly when the original natural numbers are strictly ordered.")))))));
}
