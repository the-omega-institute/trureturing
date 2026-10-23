using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeActualStrongStateStepDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStrongStateStep.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same parent joint partition earns both restored orders and all retained edge invariants.",
        H("Advance the Complete Actual State"),
        Blocks(
            Describe.Lean(DescribeId.Create("strong-state-from-same-parent"),
                DeclarationHandle.Create(Prefix + "strong_state_from_same_parent"),
                H("Construct the Next Strong State"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The current joint partition and both actual prior boundary orders earn a complete next state. Its graph map preserves raw vertices, its primary and opposite parity flags exchange, and its distinguished flag flips. The Hamilton property, literal boundary coordinates, all three partitions and all three retained-edge invariants remain attached to the same mapped parent cycle."))), DescribeRole.Theorem))));
}
