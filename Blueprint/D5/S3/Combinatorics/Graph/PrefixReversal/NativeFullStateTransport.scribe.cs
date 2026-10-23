using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeFullStateTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeFullStateTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Preserve Both Literal Native Boundary Orders.",
        H("Preserve Both Literal Native Boundary Orders"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-full-state-transport-native-actual-identity-two-order-state-transport"), DeclarationHandle.Create(Prefix + "native_actual_identity_two_order_state_transport"),
                H("Carry Joint and Both Half Partitions Together"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An inclusion that preserves raw configurations carries the joint partition and both restored half partitions of one supplied actual cycle together. Both native endpoint templates and both raw cut images remain attached to that same mapped cycle; no second witness is selected."))), DescribeRole.Theorem))));
}
