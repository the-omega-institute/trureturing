using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class GraphThickeningStableCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A categorical two-cover for first subdivisions of graph thickenings",
        H("A categorical two-cover for first subdivisions of graph thickenings"),
        Blocks(Describe.Lean(
            DescribeId.Create("graph-thickening-first-subdivision-two-cover"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/GraphThickeningStableCover.hasCategoricalCover_first_subdivision"),
            H("Two categorical lower sets cover the first subdivision"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("The poset consists of the faces of the cone on the edge subdivision of a finite simple graph, together with an extra triangular maximum over each two-edge path. The strict lower chains at an added maximum pass through one of the two side faces. The relative cover theorem extends the common cone-face region by folding towards one side on each piece. Both categorical lower sets lie in the same ordinary subdivision."))),
            DescribeRole.Theorem))));
}
