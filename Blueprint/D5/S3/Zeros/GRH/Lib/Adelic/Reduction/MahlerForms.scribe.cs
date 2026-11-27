using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Reduction;

internal sealed class MahlerFormsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mahler Forms", H("Mahler Forms"),
        Blocks(
            Paragraph(Text("Field elements with bounded denominators and very small conjugates vanish. Compactness in adelic GL_n from determinant bound; reduced bases in a compact set. Mahler-Godement criterion core: dual reduced bases have finitely many Gram matrices, form varying.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Reduction/MahlerForms.exists_finite_gram"),
                H("exists_finite_gram"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For compact K ⊂ GL_n(𝔸) there are finite F, compact C: if y*Jy ∈ K, some Y ∈ GL_n(E), d ∈ E^n have (Y*JY)_{ij} = 0 when d_i, d_j ≠ 1, ((W⁻¹y)_f, y⁻¹Z) ∈ C, (d, Z*JZ) ∈ F, for W = (Y*J)⁻¹, Z = W·diag d.")))))));
}
