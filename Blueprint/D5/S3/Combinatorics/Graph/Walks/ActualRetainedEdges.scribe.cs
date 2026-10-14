using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualRetainedEdgesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualRetainedEdges.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closing an actual piece chain preserves every retained child edge.",
        H("Actual Route Inventories"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-chain-keeps-piece-edges"),
                DeclarationHandle.Create(Prefix + "actual_chain_keeps_piece_edges"),
                H("Keep Every Piece Edge in the Chain"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every edge of any supplied piece remains in the literal chained edge list. The argument includes all intermediate pieces and makes no disjointness or Hamiltonian assumption."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-closed-route-keeps-piece-edges"),
                DeclarationHandle.Create(Prefix + "actual_closed_route_keeps_piece_edges"),
                H("Keep Every Piece Edge After Closure"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The supplied cycle has the literal reversed chain-edge inventory with its closing seam. Every edge of every constituent piece therefore belongs to that same cycle. This is the inventory lemma used by native recursive retention proofs; it supplies no independent cycle existence statement."))), DescribeRole.Theorem))));
}
