using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class LabeledZetaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Weil/LabeledZeta",
            "A labeled Dirichlet vector remains nonzero at every spectral parameter."),
        H("Labeled Zeta Vectors"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("labeled-zeta-vector-never-vanishes"),
                H("The labeled vector never vanishes"),
                LeanTheorem(
                    "D5/S3/Weil/LabeledZeta.labeled_zeta_vector_ne_zero"),
                new Formula.Layout(FormulaLayoutMode.Inline, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("A")), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexSymbol(FormulaLatexSymbol.OpenBracket), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("AddMonoid"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("A")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.CloseBracket), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Ell), new Formula.LatexSymbol(FormulaLatexSymbol.Colon), new Formula.LatexWord(FormulaIdentifier.Create("A")), new Formula.LatexMacro(FormulaLatexMacro.To), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexSymbol(FormulaLatexSymbol.Plus)]), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("R"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("C"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("labeledZeta"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Ell), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Neq), new Formula.LatexSpace(), new Formula.LatexDigits([0])])),
                DescribeProvenance.LiteratureAttested(
                    LibraryNoteRef.Create("D5/L/hedenmalm1997hilbert")),
                Blocks(Paragraph(Text(
                    "The coordinate product needs no summability claim. Its empty-ledger coordinate is one, so the kernel-checked function cannot equal the zero vector.")))
            ))));
}
