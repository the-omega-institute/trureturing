using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualPathRecoveryPrefixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualPathRecoveryPrefix.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual vertex ownership and retained edges recover literal prefixes inside supplied simple boundary paths.",
        H("Recovering Actual Path Prefixes from Retained Inventories"),
        Blocks(
            Paragraph(Text("The vertex type and simple graph are arbitrary. All paths and cycle inventories refer to the literal supplied walks. These statements provide actual graph-surgery steps; an all-order recursive Hamilton construction is a separate consumer.")),
            Describe.Lean(DescribeId.Create("actual-partition-rooted-walk-edges"),
                DeclarationHandle.Create(Prefix + "actual_partition_rooted_walk_edges"),
                H("Recover the Rooted Piece Edges"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In a family whose full support contains no repeated vertex, every edge of a supplied walk starting in one family piece belongs to that piece whenever it belongs to the global family edge inventory. Induction keeps each visited vertex with its unique actual owner."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-rooted-path-is-prefix"),
                DeclarationHandle.Create(Prefix + "actual_rooted_path_is_prefix"),
                H("Retained Edges Force a Literal Prefix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A supplied walk and a supplied simple path start at the same vertex. If the first walk has no repeated support and all of its edges occur in the simple path, it is the literal initial segment of that path. The remainder is an actual simple walk with the correct endpoints."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-restored-partition-joint-prefix"),
                DeclarationHandle.Create(Prefix + "actual_restored_partition_joint_prefix"),
                H("Recover a Joint Prefix after Restoration"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual joint and restored single-order families have duplicate-free full supports. Edges of a supplied joint walk retained by the restored family belong to its actual boundary piece, and give a literal prefix there. This conclusion uses actual edge membership rather than an assumed route factorization."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-restored-initial-joint-prefix"),
                DeclarationHandle.Create(Prefix + "actual_restored_initial_joint_prefix"),
                H("Recover the Distinguished Initial Joint Path"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact joint and single-order inventories of a supplied source walk show that the distinguished actual joint path begins its actual restored boundary. Every edge remains in that boundary, and the returned tail is simple."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-restored-bridge-route-prefix"),
                DeclarationHandle.Create(Prefix + "actual_restored_bridge_route_prefix"),
                H("Recover the Restored Crossing Prefix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual marked seam in the old restored cut group joins the reverse crossing path to the distinguished joint path. Cycle simplicity and the exact retained inventories earn the joined support simplicity, its membership in the actual boundary and the literal remaining tail."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-restored-joint-cut-position"),
                DeclarationHandle.Create(Prefix + "actual_restored_joint_cut_position"),
                H("Locate a Cut in the Recovered Prefix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A cut at a supplied index of an actual joint path has a corresponding directed index in the actual restored boundary. The previous retained-inventory prefix theorem earns that position instead of requiring it as an input."))), DescribeRole.Theorem))));
}
