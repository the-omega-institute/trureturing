using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteGraphSuspensionMoves;

internal sealed class FiniteGraphSuspensionMovesLozinDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteGraphSuspensionMoves/Lozin.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lozin moves as local star suspensions", H("Lozin moves as local star suspensions"), Blocks(
            Node("n0", "starSubgraph", "The local star",
                "The chosen center and its nonempty selected neighbor set define the local star subgraph. Edges between leaves remain ambient edges."),
            Node("n1", "lozinSuspension", "The literal Lozin replacement",
                "A partition of the center neighborhood into disjoint sets Y and Z replaces the center by a four-vertex path, with the endpoints attached to Y and Z respectively."),
            Node("n2", "lozinSuspensionIso", "Identification with the star gadget",
                "When Y is nonempty and Y,Z partition the center neighborhood, the literal replacement is isomorphic to the arbitrary-subgraph suspension of the local star."),
            Node("n3", "lozinSuspensionReducedHomologyIso", "Reduced singular homology transport",
                "For finite graphs and every q at least one, the replacement shifts actual reduced integral singular homology by one degree. The graph operation, rather than a homology premise, supplies the transport."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose, DescribeRole? role = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
