using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualOpenedChildInventoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualOpenedChildInventory.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recover the Actual Opened P Child Inventory.",
        H("Recover the Actual Opened P Child Inventory"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-opened-child-inventory-actual-opened-child-from-joint-partition"), DeclarationHandle.Create(Prefix + "actual_opened_child_from_joint_partition"),
                H("Remove the Actual Supplier Edge and Restore Old Marked Edges"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An exact previous joint partition and a supplied Hamilton supplier-complement path belong to the same child cycle. If the distinguished joint path has its actual two-edge prefix, removing the second prefix edge restores all old marked edges and earns the full support and edge permutations of the actual opened P path."))), DescribeRole.Theorem))));
}
