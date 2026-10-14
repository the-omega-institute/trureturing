using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeSimultaneousBoundaryStateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeSimultaneousBoundaryState.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Advance Both Actual Native Boundary Templates on One Cycle.",
        H("Advance Both Actual Native Boundary Templates on One Cycle"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-simultaneous-boundary-state-native-actual-simultaneous-boundary-state"), DeclarationHandle.Create(Prefix + "native_actual_simultaneous_boundary_state"),
                H("Restore Both Orders Without Reselecting the Witness"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A concrete previous joint and two-half state, its literal distinguished native ports and boundary templates, and the actual updated parent joint partition earn both next restored partitions and endpoint templates on the same supplied Hamilton cycle. The old order roles exchange. The next endpoint laws and route factorizations are conclusions, while the old state and actual new joint partition remain premises."))), DescribeRole.Theorem))));
}
