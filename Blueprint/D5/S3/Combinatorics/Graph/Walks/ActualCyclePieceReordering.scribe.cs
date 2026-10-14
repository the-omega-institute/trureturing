using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualCyclePieceReorderingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualCyclePieceReordering.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A supplied actual partition can be oriented along a route and joined while retaining exact support and edge inventories.",
        H("Reordering and Joining Actual Cycle Pieces"),
        Blocks(
            Paragraph(Text("The vertex type and simple graph are arbitrary. All paths and cycle inventories refer to the literal supplied walks. These statements provide actual graph-surgery steps; an all-order recursive Hamilton construction is a separate consumer.")),
            Describe.Lean(DescribeId.Create("actual-cycle-partition-inventory"),
                DeclarationHandle.Create(Prefix + "actual_cycle_partition_inventory"),
                H("Earn the Number of Pieces"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact full-support and filtered-edge permutations of one supplied Hamilton cycle give unique vertex coverage, the retained-edge membership and a number of pieces equal to the actual cut cardinality. Nil pieces are counted through their one support vertex."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-partition-pieces-reordered"),
                DeclarationHandle.Create(Prefix + "actual_partition_pieces_reordered"),
                H("Reorder the Supplied Actual Pieces"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every supplied piece matches a whole route edge. Unique vertex ownership makes the assignment injective, and equal finite cardinality makes it a permutation. Each selected piece is copied or reversed to the directed route endpoints; coverage and retained edges are preserved."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-cycle-slices-reordered"),
                DeclarationHandle.Create(Prefix + "actual_cycle_slices_reordered"),
                H("Reorder the Actual Slices of a Cycle"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the supplied-piece reordering to the actual slicing chosen from one Hamilton cycle and its nonempty set of actual cuts. The endpoint matching premise concerns that same chosen family."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-partition-pieces-joined"),
                DeclarationHandle.Create(Prefix + "actual_partition_pieces_joined"),
                H("Join Supplied Pieces into a Hamilton Path"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual adjacency between consecutive route endpoints joins the reordered supplied pieces into an actual Hamilton path. Its support is literally the concatenation of their full supports, and its edges are literally the actual chain inventory."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-cycle-slices-joined"),
                DeclarationHandle.Create(Prefix + "actual_cycle_slices_joined"),
                H("Join the Actual Cycle Slices"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The corresponding cycle-slicing wrapper selects its slicing once, reorders that family and joins it with the supplied real connectors. It returns the same support and retained-edge readouts."))), DescribeRole.Theorem))));
}
