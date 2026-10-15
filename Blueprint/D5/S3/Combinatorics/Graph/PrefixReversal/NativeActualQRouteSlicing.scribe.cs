using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeActualQRouteSlicingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualQRouteSlicing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Slice the Same Actual Native Q Route.",
        H("Slice the Same Actual Native Q Route"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-actual-qroute-slicing-native-actual-q-route-three-fragments"), DeclarationHandle.Create(Prefix + "native_actual_q_route_three_fragments"),
                H("Earn Both Cut Occurrences from the Old Cycle"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual joint and single-order inventories of the same native Q cycle, its protected a and remaining b invariants and literal port coordinates earn all four retained edges used by two-cut slicing. A concrete later boundary-piece position supplies the strict order, and the three output paths have the exact support and edge identities of the supplied full route."))), DescribeRole.Theorem))));
}
