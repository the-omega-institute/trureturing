using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class DisjointCoverObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Obstructions to categorical cover transport across an elementary expansion",
        H("Obstructions to categorical cover transport across an elementary expansion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("disjoint-partition-obstruction"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/DisjointCoverObstruction.disjoint_partition_obstruction"),
                H("Exact retention can fail at the inherited depth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("The retained first subdivision has a disjoint vertex partition whose induced regions are categorical. Assigning the new chamber barycentre either colour forces a six-edge cycle in that region. Under the corresponding simplicial retraction, two original cycle vertices remain distinct throughout every contiguity chain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("full-piece-with-exterior-noncategorical"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/DisjointCoverObstruction.full_piece_with_exterior_noncategorical"),
                H("The whole exterior cannot be assigned to either piece"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("At each later ordinary depth the original vertex rigidity persists on the subdivided witness. A full region that contains its prescribed old colour and all exterior vertices contains this witness, even when the proposed regions overlap."))),
                DescribeRole.Theorem))));
}
