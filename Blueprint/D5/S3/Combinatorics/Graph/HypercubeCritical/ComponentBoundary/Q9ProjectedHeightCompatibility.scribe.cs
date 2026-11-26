using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9ProjectedHeightCompatibilityDocument : IScribeDocumentDefinition
{
    private const string Cube = "D5/S3/Combinatorics/Graph/HypercubeCritical/";
    private const string Owner = Cube + "ComponentBoundary/Q9ProjectedHeightCompatibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer heights constrain the centers and splits of six-dimensional cube boxes.",
        H("Box centers are invariant along paths in the Laurent projection"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-projection-box-center"),
                DeclarationHandle.Create(Owner + "equal_center_of_overlap"),
                H("Overlap and a common height determine the center"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A box consists of the nine points obtained by flipping one axis in each part of a three-plus-three split. The two splits use left parts {0,1,2} and {0,1,3}. On each box, the height is an offset plus the bit indicator of the flips from its center.")),
                    Paragraph(Text("On a coordinate where two centers differ, the two height formulas have opposite slopes in that bit. Two overlap points with different bits give conflicting increments. Simultaneous XOR translation fixes the first center at zero, so the kernel checks only four pairs of split labels and sixty-four relative centers. The overlapping boxes then have the same center."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-projection-box-splits"),
                DeclarationHandle.Create(Owner + "no_mixed_splits_of_connected_projection"),
                H("A connected projection with threefold fibers has one split"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A path within boxes propagates the common center. Boxes in one slice are disjoint, so at most one can occur there since the two centered shapes have a common point. Each shape also has a point absent from the other. If both shapes occur, these two points each need three slices of their own shape, exceeding the four available slices.")),
                    Paragraph(Text("This is the six-axis projection obstruction for the five-direction case in Hong, Wu and Xia's Problem 2. The statement assumes the disjoint box representation, common height, threefold fibers and projected connectivity. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Cube + "CoordinateHalves/CubeBitMoves"))]));
}
