using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class GraphSubdivisionHalvesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Half-edge coordinates on a subdivided graph",
        H("Half-edge coordinates on a subdivided graph"),
        Blocks(Describe.Lean(
            DescribeId.Create("graph-subdivision-halves"),
            DeclarationHandle.Create(
                "D5/S3/Topology/GraphSubdivisionHalves.split_charts"),
            H("The distance to the midpoint has a common global realization on a graph"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "Assign each subdivided half-edge to its old endpoint and leave the midpoint unassigned. The assignments agree wherever edge charts meet. Every face has at most one assigned endpoint among its vertices, and distances from the midpoints vary by at most one along an edge. An isolated old vertex receives the same coordinate as an old endpoint."))),
            DescribeRole.Theorem))));
}
