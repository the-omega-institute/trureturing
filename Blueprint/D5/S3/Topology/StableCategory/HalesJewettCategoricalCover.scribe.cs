using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class HalesJewettCategoricalCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Categorical covers of subdivided finite powers",
        H("Categorical covers of subdivided finite powers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-no-categorical-cover"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/HalesJewettCategoricalCover.exists_no_categorical_cover"),
                H("Unbounded one-step categorical cover size for powers of a ranked poset"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("A finite alphabet of full chains contains every chain of the factor and supplies a section of the rank for each letter. A word then specifies a synchronized chain in the power. A monochromatic Hales–Jewett line forces one lower cover set to contain the image of the entire subdivided factor. Projection at any variable coordinate splits that embedding. A categorical contraction of the set would contract the subdivided factor."))),
                DescribeRole.Theorem))));
}
