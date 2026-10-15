using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualPathFamilyInventoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualPathFamilyInventory.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual path family covering each vertex once earns the full support and retained-edge inventories of the same Hamilton cycle.",
        H("Actual Path Families Retain the Same Cycle Inventory"),
        Blocks(
            Paragraph(Text("The graph and vertex type are arbitrary. The inputs are actual walks, unique vertex coverage and edge membership against one supplied Hamilton cycle. The proof derives the list permutations: it does not assume a target support permutation or select a different cycle. Nil paths retain their one vertex.")),
            Describe.Lean(DescribeId.Create("actual-path-partition-edges-nodup"),
                DeclarationHandle.Create(Prefix + "actual_path_partition_edges_nodup"),
                H("Vertex Ownership Eliminates Repeated Edges"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When the concatenation of actual piece supports has no repeated vertex, the concatenation of their edge lists has no repeated edge. A repeated edge would repeat one of its incident vertices either inside a path or across two different pieces. This live helper is used by the same-cycle family inventory and by supplier-edge restoration."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-path-family-cycle-inventory"),
                DeclarationHandle.Create(Prefix + "actual_path_family_cycle_inventory"),
                H("Earn Full Support and Exactly the Uncut Edges"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite family of actual paths covering every graph vertex in exactly one member, the concatenated supports are a permutation of the supplied Hamilton cycle's support tail. If family edge membership is exactly membership in that cycle excluding a specified finite cut set, the concatenated edges are a permutation of the cycle edge list filtered by those cuts. Simplicity and unique vertex ownership eliminate repeated edges, so membership determines the exact retained-edge inventory."))), DescribeRole.Theorem))));
}
