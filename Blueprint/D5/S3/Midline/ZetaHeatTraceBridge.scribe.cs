using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline;

internal sealed class ZetaHeatTraceBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Midline/ZetaHeatTraceBridge",
            "Prime-axis logarithmic length derives the labeled-zeta Hilbert criterion from the universal heat-abscissa theorem."),
        H("The Labeled-Zeta Heat-Trace Bridge"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("labeled-zeta-is-the-prime-axis-specialization"),
                H("Labeled zeta is the prime-axis specialization"),
                LeanTheorem(
                    "D5/S3/Midline/ZetaHeatTraceBridge.zeta_mem_iff_from_universal_heat_trace"),
                new Formula.Layout(FormulaLayoutMode.Inline, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("C"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("MemLp"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("labeledZetaCoefficient"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexDigits([2]), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Leftrightarrow), new Formula.LatexMacro(FormulaLatexMacro.Frac), new Formula.LatexDigits([1, 2]), new Formula.LatexSymbol(FormulaLatexSymbol.LessThan), new Formula.LatexMacro(FormulaLatexMacro.Re), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis)])),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The bridge identifies the universal heat coefficient with the labeled-zeta coefficient, proves boundary-divergent abscissa one by transporting to the p-series on natural addresses, and then applies the universal strict theorem.")))))));
}
