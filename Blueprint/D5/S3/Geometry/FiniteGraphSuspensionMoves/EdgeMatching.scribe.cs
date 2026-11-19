using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteGraphSuspensionMoves;

internal sealed class FiniteGraphSuspensionMovesEdgeMatchingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteGraphSuspensionMoves/EdgeMatching.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Edge and matching suspension moves", H("Edge and matching suspension moves"), Blocks(
            Node("n0", "tripleSubdivision", "Three fresh vertices",
                "The literal triple subdivision deletes only the chosen edge and replaces it by a path with three fresh internal vertices, retaining every other old edge."),
            Node("n1", "tripleSubdivisionIso", "Identification with the edge gadget",
                "The actual triple-subdivision graph is isomorphic to the local arbitrary-subgraph suspension gadget of the chosen edge."),
            Node("n2", "tripleSubdivisionReducedHomologyIso", "The integral homology shift",
                "For a nonempty finite graph, an actual chosen edge and every q at least one, triple subdivision identifies reduced integral singular homology in degree q+1 with that of the original independence realization in degree q."),
            Node("n3", "crossingSuspension", "The matching gadget",
                "Two disjoint chosen edges are replaced using a new hub and four quadrant vertices. Their endpoints may have extra ambient edges."),
            Node("n4", "crossingSuspensionReducedHomologyIso", "The matching homology shift",
                "For every injective choice of the four endpoints of two edges and every q at least one, the actual matching gadget gives the same one-degree reduced integral singular homology shift."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose, DescribeRole? role = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
