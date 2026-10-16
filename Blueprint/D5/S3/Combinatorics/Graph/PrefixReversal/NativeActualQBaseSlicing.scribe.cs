using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeActualQBaseSlicingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualQBaseSlicing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct the Exceptional Actual Native Q Split.",
        H("Construct the Exceptional Actual Native Q Split"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-actual-qbase-slicing-native-actual-q-base-three-fragments"), DeclarationHandle.Create(Prefix + "native_actual_q_base_three_fragments"),
                H("Recover the Second-Order Middle Boundary"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal second-order port coordinates identify two restored seams connecting three concrete joint pieces in the middle boundary path. The same prior cycle supplies the retained a and b edges; actual joint ownership earns both cut positions. The three resulting paths exhaust the supplied full Q route with exact support and edge identities."))), DescribeRole.Theorem))));
}
