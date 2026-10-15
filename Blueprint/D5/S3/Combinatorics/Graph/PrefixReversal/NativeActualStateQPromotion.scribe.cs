using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeActualStateQPromotionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateQPromotion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both new boundary cuts are sliced inside the special path already used by the parent.",
        H("Slice the Same Actual Q State"),
        Blocks(
            Describe.Lean(DescribeId.Create("same-state-q-three-fragments"),
                DeclarationHandle.Create(Prefix + "same_state_q_three_fragments"),
                H("Earn the Three Actual Q Fragments"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either parity, the retained Q state and its literal boundary coordinates split the previously chosen special path into three path fragments. Their support, complete edge decomposition and filtered-edge inventory refer to that same special path and the two literal new cuts."))), DescribeRole.Theorem))));
}
