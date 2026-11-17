using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class TwentyPointSliceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twenty Point Slice", H("Twenty Point Slice"),
        Blocks(
            Paragraph(Text(
                "This module records the exact actual twenty-vertex slice telescope for the Hong–Wu–Xia Section 7 Problem 2 branch. "
                    + "The support is induced in an arbitrary Boolean cube and carries original Huang balance, twenty vertices, degrees two or three, "
                    + "exactly ten degree-two vertices, and actual degree-two independence. Girth is derived from balance.")),
            Paragraph(Text(
                "The compiled local reduction constructs the cube-parity bipartition, derives girth at least eight, proves that the induced high graph has five edges, "
                    + "and reduces the parity counts to (10,10;5,5), (11,9;8,2), or the swapped orientation. It does not assume connectivity, a compressed graph, labels, "
                    + "a cycle classification, a coordinate normal form, or a signed-path result.")),
            Paragraph(Text(
                "The five-vertex classification, actual coordinate transport, and Huang-sign contradiction remain open producer work. "
                    + "The unsigned abstract twenty-vertex graph is not used as an actual cube countermodel.")),
            Describe.Lean(
                DescribeId.Create("twenty-point-slice-claim"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSlice.claim"),
                H("claim"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The literal proposition quantifies over every ambient dimension, every finite actual support, and actual bipartition sides. "
                        + "Its local hypotheses are support cardinality twenty, degree type two or three, exactly ten actual degree-two vertices, actual degree-two independence, "
                        + "and original IsBalanced."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-twenty-point-slice-data"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSlice.actual_twenty_point_slice_data"),
                H("actual twenty-point slice data"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "From claim, BalancedCubeGirth.eight_le_egirth supplies girth at least eight; actual low/high incidence counting supplies five high-high edges; "
                        + "and the constructed cube-parity bipartition supplies the three displayed parity alternatives. The final obstruction is not claimed here."))), DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/EighteenPointSlice")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighGraph"))
        ]));
}
