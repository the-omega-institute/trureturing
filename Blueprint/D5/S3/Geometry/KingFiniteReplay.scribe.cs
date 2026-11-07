using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class KingFiniteReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/KingFiniteReplay.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Forty concrete suspensions of the torsion seed", H("Forty concrete suspensions of the torsion seed"), Blocks(
            Node("n1", "fortyMoves", "The forty-move chain",
                "The literal adjacency, freshness, label-coverage and neighborhood-partition proofs assemble a MoveChain of length forty from the actual seed graph to the actual 141-vertex final graph. Local edge subgraphs need not be induced."),
            Node("n2", "reducedHomologyIso", "The complete finite-replay shift",
                "For every q at least one, reduced integral singular homology of the final independence realization in degree q+40 is isomorphic to that of the seed realization in degree q."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose, DescribeRole? role = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
