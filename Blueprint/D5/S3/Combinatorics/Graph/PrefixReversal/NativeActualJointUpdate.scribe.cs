using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeActualJointUpdateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualJointUpdate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Update the Complete Actual Native Joint Partition.",
        H("Update the Complete Actual Native Joint Partition"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-actual-joint-update-native-actual-closed-parent-joint-update"), DeclarationHandle.Create(Prefix + "native_actual_closed_parent_joint_update"),
                H("Earn the New Joint Partition on the Same Parent Cycle"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given the concrete closed parent Hamilton cycle, the actual opened old P path and its exact deleted marked-edge inventory, the actual three-fragment Q split, and the literal chain connecting the other children, the proof earns a complete next joint partition. Actual vertex counts, uncut edges, endpoint pairs, disjoint marked groups and their erase identities all refer to this same parent cycle. This is a concrete propagation interface; unconditional all-order existence is not claimed."))), DescribeRole.Theorem))));
}
