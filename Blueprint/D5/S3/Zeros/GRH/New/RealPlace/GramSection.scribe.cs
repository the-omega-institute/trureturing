using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.RealPlace;

internal sealed class GramSectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gram Section", H("Gram Section"),
        Blocks(
            Paragraph(Text("Explicit section is unitary and represents every double coset of the open cell.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/RealPlace/GramSection.exists_eq_mul_gramSection_mul"),
                H("exists_eq_mul_gramSection_mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If γ ∈ G₁ has Z(γ) in Ω, then γ = u h γ_{Z(γ)} h' u' with u, u' in the frame-fixing unipotent group U⁰ and h, h' in the image of U(κ).")))))));
}
