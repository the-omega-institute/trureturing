using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class Q9TenProjectionOnlyK4Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ten patterns in a four-coordinate projection",
        H("The subdivided K₄ projection"),
        Blocks(Describe.Lean(
            DescribeId.Create("q9-ten-pattern-projection-k4-orbit"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenProjectionOnlyK4."
                    + "ten_projection_only_k4"),
            H("A ten-pattern projection belongs to the subdivided K₄ orbit"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Take a 72-vertex Huang-balanced induced cubic support in the nine-cube "
                    + "with every coordinate half of size at least 28. Suppose a projection "
                    + "onto four distinct axes realizes ten patterns. Its projected graph "
                    + "is equivalent by coordinate reindexing and bit translation to the "
                    + "graph obtained by subdividing each edge of K₄ once.")),
                Paragraph(Text(
                    "Pair coverage gives antipodality of distinct parallel complement "
                    + "edges. Together with projected minimum degree two this leaves six "
                    + "orbits of ten-point subsets under the four-cube action. The signed "
                    + "Huang equations transport to each representative.")),
                Paragraph(Text(
                    "Two representatives lose a realized pattern through the exterior "
                    + "equations or equality of suffix supports. For another representative, "
                    + "a mixed signed sum cancels by self-adjointness and bounds a half. "
                    + "Two more have five-cube suffix carriers with six common leaves. "
                    + "Their two-center geometry forces halves of size at most 27.")),
                Paragraph(Text(
                    "In the remaining representative the four even patterns are the "
                    + "vertices of K₄ and each odd pattern is the midpoint of a distinct "
                    + "edge. The signed odd values on a suffix fiber can therefore be "
                    + "studied through cuts of K₄. This reduces a projection case in the "
                    + "order-72 branch of Hong, Wu and Xia, arXiv:2610.09483v1, Section 7, "
                    + "Problem 2."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjectionSharp")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenShadowSelfAdjoint"))
        ]));
}
