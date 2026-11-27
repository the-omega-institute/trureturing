using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.GoodReduction;

internal sealed class PeakContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Peak Contraction", H("Peak Contraction"),
        Blocks(
            Paragraph(Text("Theta identity by Schur, kernel of c keeps peaks, descent and contraction of defects.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/GoodReduction/PeakContraction.hasMultiplicativeNorm_of_expanding"),
                H("hasMultiplicativeNorm_of_expanding"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Good reduction: on a polarised torus V/L with adjoint action of an order, β + β̄ = 1, nL^∨ ⊆ L, p ∤ n, v(p) < 1, sup norms of sizes multiply if non-units c ∣ p^k coprime to c̄ with v(det c̄) = 1 have arbitrarily small inverses on V.")))))));
}
