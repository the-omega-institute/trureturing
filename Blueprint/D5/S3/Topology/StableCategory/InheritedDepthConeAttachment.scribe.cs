using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class InheritedDepthConeAttachmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cone attachments through ordinary subdivision",
        H("Cone attachments through ordinary subdivision"),
        Blocks(Describe.Lean(
            DescribeId.Create("inherited-depth-cone-two-cover"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/InheritedDepthConeAttachment.exact_two_cover_of_adjoined_maximum"),
            H("The cone of an adjoined maximum transports two prescribed traces at positive depth"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("After the first subdivision an adjoined maximum gives a cone attached to the retained region along its strict lower set. At each further subdivision, chains avoiding the apex singleton are added to the retained region and chains with entries containing the apex form the next cone. Erasing the apex lifts to a relative order fence and identifies the new base with the subdivision of the previous base. The retained retraction therefore identifies the base with the actual subdivided interface at every positive depth. A full first trace and an anchor spanning its exclusive complement then yield categorical lower pieces with both old traces after two further ordinary subdivisions."))),
            DescribeRole.Theorem))));
}
