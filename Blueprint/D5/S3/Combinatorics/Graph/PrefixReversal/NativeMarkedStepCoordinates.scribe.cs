using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeMarkedStepCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedStepCoordinates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native full tuples earn the next marked coordinates and independent child ownership.",
        H("Actual Coordinates of the Marked Step"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-marked-index-shift"), DeclarationHandle.Create(Prefix + "native_marked_index_shift"),
                H("Literal Rotation Shifts Every Positive Mark"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every supplied frame and a last base label u, the right and left native ports of nextFrame at index i+1 equal the old ports at index i. The proof computes the full permutation tuple, so the equality identifies actual configurations for all natural indices."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-q-index-zero-prefix"), DeclarationHandle.Create(Prefix + "native_q_index_zero_prefix"),
                H("The Actual New Zero Cut Prefix"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The outer frame left-zero vertex takes an a-generator step to the next frame right-zero vertex, then a b-generator step to its left-zero vertex. Both equalities concern the full native configurations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-p-parent-cut-prefix"), DeclarationHandle.Create(Prefix + "native_p_parent_cut_prefix"),
                H("The Actual Final P Supplier Cut"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The old left-zero configuration takes its a step to the final outer supplier right port, whose b step reaches the supplier left port. That same old configuration equals nextFrame left port one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-new-marked-cut-domains"), DeclarationHandle.Create(Prefix + "native_new_marked_cut_domains"),
                H("Earn Both Endpoint Child Domains"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a sufficiently long remaining base, the new mark zero has both endpoints in outer child zero, and every positive new mark has both endpoints in the final outer child. The independent Layer domain is earned by literal tuple deletion and circle rotation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-new-marked-cut-owner-iff"), DeclarationHandle.Create(Prefix + "native_new_marked_cut_owner_iff"),
                H("Exact Marked Cut Ownership"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The independent disjoint child partition upgrades endpoint membership to an iff: both endpoints of a new mark belong to outer child j exactly when j is zero for mark zero or the final gap for a positive mark. It excludes every third child without assuming a future walk."))), DescribeRole.Theorem))));
}
