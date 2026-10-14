using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ActualClosedParentJointUpdateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/ActualClosedParentJointUpdate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct the Actual Joint Partition of a Closed Parent Cycle.",
        H("Construct the Actual Joint Partition of a Closed Parent Cycle"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-closed-parent-joint-update-actual-closed-parent-joint-partition"), DeclarationHandle.Create(Prefix + "actual_closed_parent_joint_partition"),
                H("Three New Paths and Every Unchanged Old Piece"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The supplied Hamilton parent has the literal closed chain of an actual three-fragment Q path, intermediate children and the actual opened P path. Exact P source inventories and Q split identities construct three new paths while retaining all other old joint pieces. Their complete support, uncut edges, cut cardinality and endpoint-pair update belong to this same parent cycle."))), DescribeRole.Theorem))));
}
