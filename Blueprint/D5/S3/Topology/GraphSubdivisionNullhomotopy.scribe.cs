using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class GraphSubdivisionNullhomotopyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Contraction of a graph map after subdividing its source",
        H("Contraction of a graph map after subdividing its source"),
        Blocks(Describe.Lean(
            DescribeId.Create("supported-graph-map-contracts"),
            DeclarationHandle.Create(
                "D5/S3/Topology/GraphSubdivisionNullhomotopy.supported_graph_map_contracts"),
            H("Finite edge-path witnesses suffice for a contiguity contraction in a fixed target"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "For a map from a finite graph to a simplicial complex, choose a path from one target base vertex to each old vertex image. Suppose that on each oriented edge, the mapped edge is equivalent by triangle moves to the reverse of the first path followed by the second. Then beyond a common ordinary subdivision depth, every choice of a vertex in each original support gives a map contiguous through a finite chain to the base vertex. Parametrize each subdivided edge by an interval, replace its map by the two paths through the midpoint while fixing the endpoints, and contract the half paths together."))),
            DescribeRole.Theorem))));
}
