using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeActualStateJointPromotionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateJointPromotion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The new joint partition uses the actual P opening, actual Q fragments and saved parent cycle.",
        H("Promote the Same Parent Joint Partition"),
        Blocks(
            Describe.Lean(DescribeId.Create("current-joint-from-same-state-parent"),
                DeclarationHandle.Create(Prefix + "current_joint_from_same_state_parent"),
                H("Earn the Current Joint Partition on the Saved Parent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original P split and the three Q fragments are joined through the saved child chain. The resulting joint partition lies on the same parent cycle; its two cut groups are disjoint, have their literal native images, and erase to the opposite old cut groups under the actual P lift."))), DescribeRole.Theorem))));
}
