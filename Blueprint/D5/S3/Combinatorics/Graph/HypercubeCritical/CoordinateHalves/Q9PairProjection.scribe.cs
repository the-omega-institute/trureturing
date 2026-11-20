using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

// Q9 scoped cache qualification.
internal sealed class Q9PairProjectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-coordinate projections of a balanced cubic nine-cube support",
        H("Every coordinate pair attains all four patterns"),
        Blocks(Describe.Lean(
            DescribeId.Create("q9-pair-projection-surjective"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairProjection."
                    + "pair_projection_surjective"),
            H("Surjectivity of the two-coordinate projections"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Consider a 72-vertex Huang-balanced induced cubic support in the nine-cube, "
                    + "with at least 30 vertices on either side of each coordinate. A missing "
                    + "two-bit pattern makes the two specified sides disjoint. At most twelve "
                    + "vertices lie in the opposite two-bit fiber.")),
                Paragraph(Text(
                    "The Huang operator gives twelve edges in each direction. The endpoints "
                    + "opposite the missing pattern all lie in that fiber, so both sets of "
                    + "endpoints fill it. A third edge at any vertex stays in the fiber. "
                    + "Applying one projected coordinate flip at both endpoints creates a "
                    + "square, which Huang balance forbids.")),
                Paragraph(Text(
                    "The statement quantifies over every coordinate pair and every bit pattern. "
                    + "It excludes all translates and coordinate permutations of the nine-point "
                    + "grid projection in the order-72 case of Hong, Wu and Xia, arXiv:2610.09483v1, "
                    + "Section 7, Problem 2. The value of f₂(Q₉) remains open in this development."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth"))
        ]));
}
