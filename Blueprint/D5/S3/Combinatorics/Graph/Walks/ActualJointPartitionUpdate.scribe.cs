using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualJointPartitionUpdateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualJointPartitionUpdate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recombined actual paths exhaust the supplied Hamilton cycle and retain exactly its uncut edges.",
        H("An Exhaustive Actual Joint Partition Update"),
        Blocks(
            Paragraph(Text("The vertex type and simple graph are arbitrary. All paths and cycle inventories refer to the literal supplied walks. These statements provide actual graph-surgery steps; an all-order recursive Hamilton construction is a separate consumer.")),
            Describe.Lean(DescribeId.Create("actual-joint-partition-of-cycle-inventory"),
                DeclarationHandle.Create(Prefix + "actual_joint_partition_of_cycle_inventory"),
                H("Recover the Whole New Actual Partition"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full support and edge inventories of one supplied Hamilton cycle include the actual P tail, route, connector, retained a edge and old deleted marks. Recombine the three actual paths and keep every other supplied piece. The result covers every vertex once, retains exactly the filtered cycle edges and has a number of pieces equal to cut cardinality. Source-cycle simplicity proves cut distinctness and prevents deleted supplier edges from being reintroduced."))), DescribeRole.Theorem))));
}
