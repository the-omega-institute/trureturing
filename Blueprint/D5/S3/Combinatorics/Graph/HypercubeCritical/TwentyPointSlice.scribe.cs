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
                "The local reduction constructs the cube-parity bipartition, derives girth at least eight, proves that the induced high graph has five edges, "
                    + "and excludes both 11/9 orientations by the derived actual theta and its cube nonembedding, leaving (10,10;5,5). It does not assume connectivity, a compressed graph, labels, "
                    + "a cycle classification, a coordinate normal form, or a signed-path result.")),
            Paragraph(Text(
                "The two five-vertex compressed graphs are each classified as a five-cycle or a four-cycle with a leaf, and the mixed pair is excluded. "
                    + "The actual paired-pentagon case is excluded by its derived matching, constant-or-injective matching directions, coordinate differences, low independence, and the original Huang negative ten-cycle. Only the paired squares with leaves remain. Their high vertices receive derived graph isomorphisms and the exact actual high-edge table a2-b4, a4-b4, a4-b2, a1-b1, a3-b3. "
                    + "The unsigned abstract twenty-vertex graph is not used as an actual cube countermodel.")),
            Describe.Lean(
                DescribeId.Create("twenty-point-slice-claim"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSlice.claim"),
                H("claim"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The literal proposition quantifies over every ambient dimension, every finite actual support, and actual bipartition sides. "
                        + "Its local hypotheses are support cardinality twenty, degree type two or three, exactly ten actual degree-two vertices, actual degree-two independence, "
                        + "and original IsBalanced."))), DescribeRole.Definition)),

        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/EighteenPointSlice")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighGraph")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointGeometry")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSymmetric")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSquareLeaf"))
        ]));
}
