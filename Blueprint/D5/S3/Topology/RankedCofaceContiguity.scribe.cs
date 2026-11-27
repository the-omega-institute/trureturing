using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class RankedCofaceContiguityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ranked contiguity for coface selections",
        H("Ranked contiguity for coface selections"),
        Blocks(Describe.Lean(
            DescribeId.Create("ranked-coface-contiguity"),
            DeclarationHandle.Create(
                "D5/S3/Topology/RankedCofaceContiguity.exists_relative_contiguity_of_chain_map"),
            H("A coface selection gives a relative contiguity chain"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "Let the source preorder have a bounded strictly increasing natural rank. " +
                "Suppose a map sends chains to chains and lies pointwise above an order map. " +
                "Update the higher ranks first. Whenever a source chain contains both updated and unchanged vertices, an unchanged vertex below an updated one has its old image below the new image of the updated vertex. " +
                "The images from each successive pair of stages form a single chain, and the two maps' agreement vertices stay fixed."))),
            DescribeRole.Theorem))));
}
