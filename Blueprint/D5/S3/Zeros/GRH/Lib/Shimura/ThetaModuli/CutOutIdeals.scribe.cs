using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.ThetaModuli;

internal sealed class CutOutIdealsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cut Out Ideals", H("Cut Out Ideals"),
        Blocks(
            Paragraph(Text("Flatness over a local ring from constant Hilbert ranks, by standard monomials and determinants.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/ThetaModuli/CutOutIdeals.map_eq_and_flat_of_isCutOut"),
                H("map_eq_and_flat_of_isCutOut"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let φ : A → k be local, ψ n : A → K jointly injective, r > 1. Assume IsCutDegree, and IsCutOut for I₀ at φ(P) and I n at ψ n(P). Then T = ⋂ (ψ n)⁻¹(I n) extends along φ to I₀, and A[X]/T is A-flat.")))))));
}
