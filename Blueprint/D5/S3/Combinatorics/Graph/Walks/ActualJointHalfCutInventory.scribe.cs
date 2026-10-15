using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualJointHalfCutInventoryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualJointHalfCutInventory.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same supplied cycle earns the exact regrouped edge inventories for half restoration.",
        H("Restoring Actual Cut Groups of the Same Cycle"),
        Blocks(
            Paragraph(Text("All walks and partitions concern the literal supplied cycles. The prior cycle can be included in a larger graph without assuming that it is Hamiltonian there. The current boundary outputs keep their actual walk identities and exact inventories.")),
            Describe.Lean(DescribeId.Create("actual-restored-single-order-inventory"),
                DeclarationHandle.Create(Prefix + "actual_restored_single_order_inventory"),
                H("Recover the Single-Order Retained Inventory"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two disjoint cut groups and actual joint and single-order filtered inventories refer to the same supplied cycle. Restoring the opposite cut group earns the single-order edge permutation from the actual joint edges followed by those restored cuts."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-prior-single-order-partition-inventories"),
                DeclarationHandle.Create(Prefix + "actual_prior_single_order_partition_inventories"),
                H("Recover the Prior Actual Regroupings"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual joint and single-order families have support permutations to the same nonrepeating cycle tail. They yield simple single-order support, the exact joint-support permutation and the exact restored-edge permutation needed by the next boundary step."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-joint-half-cut-inventory"),
                DeclarationHandle.Create(Prefix + "actual_joint_half_cut_inventory"),
                H("Isolate the New Opposite-Order Cut"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The joint retained inventory and actual cut membership partition the complete source cycle edge list. One supplied seam in the restored group is isolated after the other restored cuts. Disjointness proves that this seam is absent from the still-deleted group and that the remaining restored cuts stay disjoint."))), DescribeRole.Theorem))));
}
