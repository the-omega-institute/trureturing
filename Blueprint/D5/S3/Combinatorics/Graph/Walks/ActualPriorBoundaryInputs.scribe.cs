using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualPriorBoundaryInputsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualPriorBoundaryInputs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Verified partitions of one supplied prior cycle earn the literal route inputs for the next boundary update.",
        H("Recovering Actual Prior Boundary Inputs"),
        Blocks(
            Paragraph(Text("All walks and partitions concern the literal supplied cycles. The prior cycle can be included in a larger graph without assuming that it is Hamiltonian there. The current boundary outputs keep their actual walk identities and exact inventories.")),
            Describe.Lean(DescribeId.Create("actual-prior-primary-boundary-inputs"),
                DeclarationHandle.Create(Prefix + "actual_prior_primary_boundary_inputs"),
                H("Recover the Actual Primary Prefix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual joint and primary partitions of the same prior cycle earn simplicity, exact support and edge regroupings and a literal primary factorization beginning with the distinguished joint walk. Its returned tail is an actual simple walk."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-prior-opposite-boundary-inputs"),
                DeclarationHandle.Create(Prefix + "actual_prior_opposite_boundary_inputs"),
                H("Recover the Actual Opposite Crossing Prefix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual old seam joins the reverse crossing piece to the distinguished joint path. The same prior cycle inventories earn every edge of that prefix, its nonrepeating support and its literal position at the start of the supplied opposite boundary, including a simple remaining tail."))), DescribeRole.Theorem))));
}
