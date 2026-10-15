using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeActualPJointPrefixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualPJointPrefix.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Earn the Actual Native P Prefix and Retained Q Cuts.",
        H("Earn the Actual Native P Prefix and Retained Q Cuts"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-actual-pjoint-prefix-native-actual-p-joint-prefix"), DeclarationHandle.Create(Prefix + "native_actual_p_joint_prefix"),
                H("Derive the Literal Two-Edge P Prefix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Protected a and remaining b invariants of the actual old cycle, together with its exact joint inventory and native coordinates, earn the distinguished path two-edge prefix and the remaining actual tail. The supplier b edge has an unselected base terminal and differs from both old marked cut groups."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-actual-pjoint-prefix-native-actual-q-zero-cut-retained"), DeclarationHandle.Create(Prefix + "native_actual_q_zero_cut_retained"),
                H("Locate the Actual Retained Q Prefix Edges"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual old Q cycle invariants and literal next-frame zero-port coordinates imply that both new prefix edges occur in the old joint pieces. Terminal labels distinguish the new b edge from every supplier cut, and the a edge joins two unprotected remaining labels. The two endpoint vertices are proved distinct."))), DescribeRole.Theorem))));
}
