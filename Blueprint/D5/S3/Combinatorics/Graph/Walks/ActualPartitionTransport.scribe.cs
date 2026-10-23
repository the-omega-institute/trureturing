using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualPartitionTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualPartitionTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Map the same cycle, pieces and cuts through an injective graph homomorphism.",
        H("Actual Route Inventories"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-cycle-partition-map"),
                DeclarationHandle.Create(Prefix + "actual_cycle_partition_map"),
                H("Transport an Actual Cycle Partition"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An injective graph homomorphism maps the supplied cycle, every actual piece and every removed cut together. The same mapped cycle remains a cycle; all mapped pieces are simple paths, their supports permute its support tail, their edges permute its exact filtered edge list, and every mapped cut belongs to it. No replacement partition certificate is assumed."))), DescribeRole.Theorem))));
}
