using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GroundRightCurrentTransport;

internal sealed class FirstSourceCompatibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Matching-sector first-source compatibility", H("FirstSourceCompatibility"), Blocks(
            Describe.Lean(DescribeId.Create("compatible-add-left"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/GroundRightCurrentTransport/FirstSourceCompatibility.compatible_add_left"),
                H("compatible_add_left"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("Original compatibility is closed under addition in the first source, with all three finite supports preserved."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sector-project-first-source-compatibility"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/GroundRightCurrentTransport/FirstSourceCompatibility.sectorProject_first_source_compatibility"),
                H("sectorProject_first_source_compatibility"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The actual finite theta-source expansion is consumed term by term. For every lattice datum, unit determinant proof, source and target vectors, sector and matching lift, the projected first source is OriginalCompatible at the requested lift. The proof retains arbitrary target vectors, signed modes and the original physical-slice carrier.")),
                    Paragraph(Text("The remaining audit gap is the lawful source-selection, whole-family variation, sensitivity and observational-dependence evidence required for four-slot registration; this is disclosed under the existing concrete issue #20510."))), DescribeRole.Theorem))));
}
