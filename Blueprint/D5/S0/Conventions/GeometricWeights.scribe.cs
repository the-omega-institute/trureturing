using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class GeometricWeightsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Conventions/GeometricWeights",
            "No nonzero rational rescaling of geometric weights matches every singleton W weight."),
        H("Geometric Weights No-Go"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("geometric-weights-do-not-match-singleton-w-weights"),
                H("Geometric weights do not match singleton W weights"),
                LeanTheorem(
                    "D5/S0/Conventions/GeometricWeights."
                    + "no_geometric_weights_match_zeckendorf_singletons"),
                GeometricNoGoFormula(),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The W-digit convention defines wValue k as fib(k+2), so singleton bits have "
                    + "weights 1, 2, 3 at indices 0, 1, 2. The first two equations force the "
                    + "geometric ratio to be 2, while the third requires its square to be 3; "
                    + "the nonzero scale excludes cancellation.")))))));

    private static Formula GeometricNoGoFormula()
    {
        Formula equation = Equal(
            Multiply(Id("w1"), new Formula.Power(Id("Lambda"), Id("k"))),
            Multiply(Id("c"), new Formula.Subscript(Id("F"), Add(Id("k"), Num(2)))));
        Formula allIndices = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            Id("Naturals"),
            equation);
        return new Formula.Layout(FormulaLayoutMode.Inline, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Neg), new Formula.LatexMacro(FormulaLatexMacro.Exists), new Formula.LatexMacro(FormulaLatexMacro.ThinSpace), new Formula.LatexWord(FormulaIdentifier.Create("w")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexDigits([1]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.Lambda), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("c")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Q"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexWord(FormulaIdentifier.Create("c")), new Formula.LatexMacro(FormulaLatexMacro.Neq), new Formula.LatexDigits([0]), new Formula.LatexSymbol(FormulaLatexSymbol.Colon), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexWord(FormulaIdentifier.Create("w")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexDigits([1]), new Formula.LatexMacro(FormulaLatexMacro.Lambda), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexWord(FormulaIdentifier.Create("cF")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexDigits([2])]), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Text), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("for")), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("every")), new Formula.LatexSpace()]), new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexMacro(FormulaLatexMacro.Ge), new Formula.LatexDigits([0]), new Formula.LatexSymbol(FormulaLatexSymbol.Period)]));
    }
}
