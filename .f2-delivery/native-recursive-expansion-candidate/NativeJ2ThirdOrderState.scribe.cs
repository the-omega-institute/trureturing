using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2ThirdOrderStateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ThirdOrderState.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Initialize every field of the actual third-order native induction state from the literal J2 parent and its retained suppliers.",
        H("A Complete Actual Third-Order State"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-j2-parent-third-order-state"),
                DeclarationHandle.Create(Prefix + "native_j2_parent_third_order_state"),
                H("Initialize the State from One Retained J2 Parent"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any actual outer J2 parent witness, the eight concrete joint paths and three retained-edge invariants construct the full StateFor of its next reversed-selected frame. The construction transports the same parent walk through identity maps on configurations, restores the primary O3 and opposite E3 partitions, and fixes the primary, opposite and distinguished orientation flags. It supplies both canonical marked cut sets, all literal endpoint coordinates, the first retained cut, protected a edges, remaining b edges and the selected-terminal c restriction. It does not assume a separately chosen cycle or a pre-existing full third-order state."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-third-order-state-exists"),
                DeclarationHandle.Create(Prefix + "native_third_order_state_exists"),
                H("Initialize Every Three-Selected-Label Frame"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every literal supply frame with three selected labels and a base of length at least three has the complete actual induction state, with primary odd, opposite even and primary distinguished orientation. A predecessor frame and its actual J2 P and Q suppliers produce the parent, and the two protected-label exchanges return the original supplied frame. The theorem resolves the third-order base only; construction of the general higher-order recursive step and unconditional all-order existence remain separate obligations."))),
                DescribeRole.Theorem))));
}
