using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Exchange;

internal sealed class TriangleNormsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triangle Norms", H("Triangle Norms"),
        Blocks(
            Paragraph(Text("Abstract triangle of maps: chains are injective, Gram determinant factors over first arrows.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Exchange/TriangleNorms.inner_weightedChain_eq"),
                H("inner_weightedChain_eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("In a triangle with G, let w₀⟪a x, a s y⟫ = ⟪x, s S_i y⟫ for the first arrow a of each row i < m. For i + n = m the weighted n-chain of row i has Gram form κ(w₀w₁ⁿ/w_n)⟪x, s T y⟫, det T = ∏_{i≤k<m} det S_k, with M(n², κ).")))))));
}
