using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJointMarkedCutShiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJointMarkedCutShift.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Native Marked Cut Sets.",
        H("Exact Native Marked Cut Sets"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-frame-marked-cuts-shift"), DeclarationHandle.Create(Prefix + "native_frame_marked_cuts_shift"),
                H("Shift One Complete Cut Group"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a supplied frame with base A followed by u, every positive cut in nextFrame is the same actual edge as a prior cut. The complete new group is the prior group with exactly its new zero edge inserted; no unlisted index is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-joint-marked-cuts-shift"), DeclarationHandle.Create(Prefix + "native_joint_marked_cuts_shift"),
                H("Shift Both Marked Orders Together"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For two prior selected orders with the same remaining base A followed by u, the union of both next cut groups equals the union of both prior groups together with the two actual new zero edges. The next orders exchange the prior orders, preserving literal configurations."))), DescribeRole.Theorem))));
}
