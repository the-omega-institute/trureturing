using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeActualStateTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Preserve Actual Native Partitions Under Identity Maps.",
        H("Preserve Actual Native Partitions Under Identity Maps"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-actual-state-transport-native-actual-identity-partition-transport"), DeclarationHandle.Create(Prefix + "native_actual_identity_partition_transport"),
                H("One Cycle and Its Exact Partition Under an Inclusion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A graph inclusion that preserves every raw configuration transports a supplied actual cycle, its concrete path pieces and cuts together. Exact support permutations, filtered edge permutations, cut membership and all raw endpoint, support and edge identities concern the same mapped walk; the image may be a proper child of the target graph."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-actual-state-transport-native-actual-parent-partition-next-marked"), DeclarationHandle.Create(Prefix + "native_actual_parent_partition_next_marked"),
                H("The Same Parent Cycle Is the Next Marked Cycle"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The independently proved parent-to-next domain identification maps a supplied Hamilton cycle and its concrete partition to the next marked domain. The complete vertex count law comes from that same Hamilton cycle, while exact retained edges and endpoint-pair images preserve their original identities."))), DescribeRole.Theorem))));
}
