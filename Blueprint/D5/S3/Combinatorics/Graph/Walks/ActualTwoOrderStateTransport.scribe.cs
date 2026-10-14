using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualTwoOrderStateTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualTwoOrderStateTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Map One Cycle and Both Marked Orders Together.",
        H("Map One Cycle and Both Marked Orders Together"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-two-order-state-transport-actual-two-order-state-map"), DeclarationHandle.Create(Prefix + "actual_two_order_state_map"),
                H("Transport the Complete Simultaneous State"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An injective graph map carries all three literal partitions of one supplied actual cycle, both marked cut groups and their disjointness to the same mapped cycle. Every resulting piece is the actual image of its source piece, including for a proper graph inclusion."))), DescribeRole.Theorem))));
}
