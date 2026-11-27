using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.RealPlace;

internal sealed class GramSectionBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gram Section Bounds", H("Gram Section Bounds"),
        Blocks(
            Paragraph(Text("Definition of open-cell section, its domain, differentiability, norm and derivative bounds.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/RealPlace/GramSectionBounds.norm_sectionMatrix_le"),
                H("norm_sectionMatrix_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let r > 0, P ≥ 8, and let every y within r of Z lie in Ω with ‖y⁻¹‖, ‖y‖, δ(y)^{−1/2} ≤ P. Then the matrix of γ_Z has norm ≤ P¹², and its real derivative in Z has norm ≤ 2P¹²/r.")))))));
}
