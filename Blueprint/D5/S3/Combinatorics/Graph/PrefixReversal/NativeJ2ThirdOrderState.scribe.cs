using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2ThirdOrderStateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ThirdOrderState.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same actual J2 outer parent initializes every field of the full third-order induction state.",
        H("Initialize the Complete Third-Order State"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-j2-parent-third-order-state"),
                DeclarationHandle.Create(Prefix + "native_j2_parent_third_order_state"),
                H("Transport the Same Parent and Its Eight Actual Paths"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal eight-piece joint partition is transported along the bijection that preserves every configuration. Both restored partitions and the three retained-edge invariants belong to that same cycle. The resulting third-order state has primary odd, opposite even and the primary distinguished far endpoint."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-third-order-state-exists"),
                DeclarationHandle.Create(Prefix + "native_third_order_state_exists"),
                H("Construct the Complete State for Every Third-Order Frame"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every supplied frame with three selected labels and at least three base labels receives a full actual state. Its predecessor supplies native P and Q witnesses. Reversing the selected order twice returns the original frame, so the construction retains the precise supplied frame and all three orientation flags. This is the base consumed by the all-order state induction."))), DescribeRole.Theorem))));
}
