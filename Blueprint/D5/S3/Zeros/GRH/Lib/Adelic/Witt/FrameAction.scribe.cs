using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Witt;

internal sealed class FrameActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frame Action", H("Frame Action"),
        Blocks(
            Paragraph(Text("Left invertible and primitive matrices, hermitian symmetry, quasi-reflections. Hermite normal form over valuation-like pairs of rings; primitive bases of flags. Witt's extension theorem for hermitian forms over a field, by quasi-reflections. Action of the unipotent subgroups on the frame; transformation of the Gram matrix.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Witt/FrameAction.eq_one_of_mem_besselU_of_fix"),
                H("eq_one_of_mem_besselU_of_fix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("An element of the unipotent group 𝖴 that fixes ϱ vectors whose coordinates at e*₁, …, e*_ϱ form the identity matrix is 1.")))))));
}
