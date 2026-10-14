using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualSingleOrderBoundaryUpdateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualSingleOrderBoundaryUpdate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal replacement of the old joint path yields exhaustive actual boundaries of one supplied current cycle.",
        H("Updating Actual Single-Order Boundaries"),
        Blocks(
            Paragraph(Text("All walks and partitions concern the literal supplied cycles. The prior cycle can be included in a larger graph without assuming that it is Hamiltonian there. The current boundary outputs keep their actual walk identities and exact inventories.")),
            Describe.Lean(DescribeId.Create("actual-single-order-boundary-update"),
                DeclarationHandle.Create(Prefix + "actual_single_order_boundary_update"),
                H("Restore the Second Q Cut"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual old boundary route passes through the distinguished joint path. Replace that path by the three actual current joint walks and restore their second Q cut. Source support and edge inventories earn two simple boundary walks, complete unique vertex coverage, exact filtered edges and the complete updated endpoint-pair set. All old boundary pieces outside this route are retained."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-single-order-first-cut-boundary-update"),
                DeclarationHandle.Create(Prefix + "actual_single_order_first_cut_boundary_update"),
                H("Restore the First Q Cut"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Restoring the first Q cut instead joins the reversed middle walk to the reversed first walk on the other side. The output again gives two literal simple boundary walks, the full current-cycle vertex partition, exact retained edges and the earned endpoint update. The final walk identities expose the actual construction."))), DescribeRole.Theorem))));
}
