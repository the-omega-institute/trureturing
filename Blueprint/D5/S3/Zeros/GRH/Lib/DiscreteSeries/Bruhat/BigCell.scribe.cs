using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Bruhat;

internal sealed class BigCellDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Big Cell", H("Big Cell"),
        Blocks(
            Paragraph(Text("Product integrals, measurability, and L² bounds of integral operators multiply over products. The unipotent character written as a trace against a matrix. Heisenberg floors, their measures, quadric charts and convolution towers over an abstract place. Open Bruhat cell of a unitary group: existence from nonzero minors, and uniqueness.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Bruhat/BigCell.exists_big_cell_decomp"),
                H("exists_big_cell_decomp"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Bruhat's big cell: over a field with involution and an element of trace 1, if all leading minors of Z(γ) are nonzero, then γ = u⁻¹w_pσu' with u, u' in 𝖴, w_p a Weyl element of length ϱ and σ in U(X₀ ⊕ Az).")))))));
}
