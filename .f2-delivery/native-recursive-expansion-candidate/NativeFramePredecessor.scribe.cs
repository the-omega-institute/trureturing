using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeFramePredecessorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeFramePredecessor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An Actual Predecessor for Every Supplied Frame.",
        H("An Actual Predecessor for Every Supplied Frame"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-frame-predecessor"), DeclarationHandle.Create(Prefix + "native_frame_predecessor"),
                H("Recover Every Next Frame"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every supplied frame with k+1 selected labels is exactly nextFrame of a prior k-label frame. The prior base is the supplied base followed by the first supplied selected label. The terminal is unchanged, the prior base is one label longer, and for k at least two the last two protected selected labels retain their identities. This proves that induction covers arbitrary supplied frames rather than only generated frames."))), DescribeRole.Theorem))));
}
