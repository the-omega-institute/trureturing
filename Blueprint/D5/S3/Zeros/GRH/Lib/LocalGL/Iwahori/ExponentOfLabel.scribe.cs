using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Iwahori;

internal sealed class ExponentOfLabelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exponent Of Label", H("Exponent Of Label"),
        Blocks(
            Paragraph(Text("Depth-zero type induced from determinant characters yields a sorted tame Iwahori eigenvector.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Iwahori/ExponentOfLabel.exists_sorted_of_detChar"),
                H("exists_sorted_of_detChar"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let ρ be smooth unitary, cyclic subrepresentations having finite-dimensional I₁-invariants; χ_a distinct, ∑m_a = N, Y = ∏_a (χ_a∘det in dimension m_a), x fixed by 1+𝔭M_N(𝒪), ∑ conj Y(g) g x ≠ 0. Then translates of x span a ξ-eigenvector, |ξ_i(ϖ)| non-increasing, ξ_i = χ_a on units m_a times.")))))));
}
