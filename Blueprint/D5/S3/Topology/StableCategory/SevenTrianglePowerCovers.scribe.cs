using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class SevenTrianglePowerCoversDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Categorical covers of powers of the seven-triangle disk",
        H("Categorical covers of powers of the seven-triangle disk"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("seven-triangles-exists-no-categorical-cover"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/SevenTrianglePowerCovers.seven_triangles_exists_no_categorical_cover"),
                H("Subdivided powers of the seven-triangle face poset have unbounded cover size"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("Rank is face cardinality minus one. Any flag extends to a vertex, edge and triangle. The boundary fixes two original vertices throughout a contiguity fence, supplying the one-piece obstruction for the Hales–Jewett argument."))),
                DescribeRole.Theorem))));
}
