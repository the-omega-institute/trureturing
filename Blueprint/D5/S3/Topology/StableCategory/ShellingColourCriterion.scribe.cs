using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class ShellingColourCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two categorical pieces from a shelling",
        H("Two categorical pieces from a shelling"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mixed-restriction-face-cover"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/ShellingColourCriterion.has_categorical_cover_of_mixed_restrictions"),
                H("A two-colour criterion on shelling restriction faces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("Fix a vertex colouring with two colours. When every nonsingleton restriction face uses both colours, the corresponding attachment leaves the two induced complexes intact. A singleton restriction face introduces one vertex. Its monochromatic faces either form an isolated point or fold onto the old monochromatic complex by sending that vertex to an old vertex of the same colour. In a connected ambient complex the two colour inclusions contract by contiguity. They give a categorical lower cover after one subdivision of the face poset."))),
                DescribeRole.Theorem))));
}
