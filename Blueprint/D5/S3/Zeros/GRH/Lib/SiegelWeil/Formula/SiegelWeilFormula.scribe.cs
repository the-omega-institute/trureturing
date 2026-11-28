using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.SiegelWeil.Formula;

internal sealed class SiegelWeilFormulaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Siegel Weil Formula", H("Siegel Weil Formula"),
        Blocks(
            Paragraph(Text("Siegel–Weil formula in the convergent range. Here a split space of rank 2p is paired with a hermitian space of rank above 2p, both unimodular at every finite place, over a CM field with the 5040th roots of unity. The Eisenstein series is a sum over Lagrangians, and the proof uses one Hecke operator at a split place against the positive Eisenstein series. Source: A. Weil, Sur la formule de Siegel dans la théorie des groupes classiques, Acta Math. 113 (1965), n° 52 Thm 5; method of proof after Andrianov (1979), Harris (1981), P. Garrett, The Siegel-Weil formula in the convergent range (notes, 2005).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/SiegelWeil/Formula/SiegelWeilFormula.siegel_weil"),
                H("siegel_weil"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Siegel–Weil formula: for S split of rank 2p and rk T > 2p, the norms of the zero terms ev_L are summable over the Lagrangians L of S, and for every f, h ↦ θ(ω(1,h)f) is integrable on [U(T)] with mean ∑_L ev_L f.")))))));
}
