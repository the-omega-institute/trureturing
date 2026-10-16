using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeThirdOrderBoundaryBaseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeThirdOrderBoundaryBase.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Restore the Actual Native Third-Order Base State.",
        H("Restore the Actual Native Third-Order Base State"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-third-order-boundary-base-native-third-order-boundary-base"), DeclarationHandle.Create(Prefix + "native_third_order_boundary_base"),
                H("Earn Both Native Templates from Eight Actual Paths"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Eight supplied actual third-order joint paths exhaust the same Hamilton cycle. Their literal native port coordinates earn both marked cut groups and the O3 and E3 restored boundary templates, including the distinguished-path and crossing identities. The theorem restores this concrete eight-path configuration and does not itself construct the eight paths or prove unconditional all-order existence."))), DescribeRole.Theorem))));
}
