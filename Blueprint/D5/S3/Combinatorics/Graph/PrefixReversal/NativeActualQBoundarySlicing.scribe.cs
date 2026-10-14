using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeActualQBoundarySlicingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualQBoundarySlicing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Earn Two-Cut Q Slicing from Literal Even and Odd Routes.",
        H("Earn Two-Cut Q Slicing from Literal Even and Odd Routes"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-actual-qboundary-slicing-native-actual-q-even-three-fragments"), DeclarationHandle.Create(Prefix + "native_actual_q_even_three_fragments"),
                H("Use the Exact Even Native Piece Position"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The supplied actual ordered even boundary pieces and their exact route endpoints place the zero left port at index s+1, after the first rooted joint piece. Together with the same cycle joint inventory and retained-edge invariants, this earns three paths that exhaust the supplied Hamilton Q route and preserve its literal support and edge split."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-actual-qboundary-slicing-native-actual-q-odd-three-fragments"), DeclarationHandle.Create(Prefix + "native_actual_q_odd_three_fragments"),
                H("Use the Exact Odd Native Piece Position"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The supplied actual ordered odd boundary pieces put the zero left port at index s+1, including the empty-ladder order-three case. Exact endpoints, the same cycle inventories and its retained-edge invariants earn the three-fragment split of that supplied Hamilton Q route."))), DescribeRole.Theorem))));
}
