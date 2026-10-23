using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeActualStateExistenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualStateExistence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native induction constructs one actual cycle with all simultaneous state data at every order at least three.",
        H("Actual Native States at Every Order"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-actual-state-exists"),
                DeclarationHandle.Create(Prefix + "native_actual_state_exists"),
                H("Construct the Complete State for the Supplied Frame"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every supplied frame with at least three selected labels and at least three base labels, the induction yields an actual Hamilton cycle in its marked domain. Its joint partition and both restored partitions use that same cycle and retain their literal ports. The state includes the protected-a, remaining-b and selected-c edge invariants. The orientation flags are the stated parity functions of the selected-label count. The third-order base is constructed from its own same-parent eight-piece partition; the successor uses the retained old states to choose its children once and carries their actual walk identities through the parent and boundary updates. The induction preserves the supplied frame rather than replacing it by a frame with only the same label sets. The final full-domain Hamilton cycle is a separate consumer of this state."))), DescribeRole.Theorem))));
}
