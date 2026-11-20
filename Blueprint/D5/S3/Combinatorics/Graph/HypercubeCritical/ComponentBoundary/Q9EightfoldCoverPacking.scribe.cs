using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9EightfoldCoverPackingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightfoldCoverPacking.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Packing eightfold exterior covers",
        H("Packing eightfold exterior covers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-eightfold-cover-packing"),
                DeclarationHandle.Create(Prefix + "thirtyTwo_mul_card_eightfoldCoverEdges_le"),
                H("Packing eightfold exterior covers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("An exterior edge with eight parallel covers forces 16 selected first- "
                        + "shell vertices and 16 selected corners. Different eightfold edges "
                        + "force disjoint sets of both shells.")),
                    Paragraph(Text("Each unordered edge therefore accounts for 32 distinct vertices of "
                        + "the balanced component. A component of order at most 186 can support "
                        + "at most five such edges."))),
                DescribeRole.Theorem)),
        []));
}
