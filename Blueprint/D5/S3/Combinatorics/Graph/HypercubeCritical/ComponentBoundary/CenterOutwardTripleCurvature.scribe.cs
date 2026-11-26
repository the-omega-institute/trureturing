using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class CenterOutwardTripleCurvatureDocument : IScribeDocumentDefinition
{
    private const string Boundary = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Module = Boundary + "CenterOutwardTripleCurvature";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Curvature of closed residuals on single-active private coordinates",
        H("Curvature of closed residuals on single-active private coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("center-fixed-bit-closed-vanishing"),
                DeclarationHandle.Create(Module + ".closed_eq_zero_of_fixed_center_bit"),
                H("A closed vector supported in a center-bit slice vanishes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the flip of a nonzero support point across this coordinate, "
                    + "only the term in that coordinate can contribute. A nonzero "
                    + "coordinate weight and unit Huang edge sign force the value to vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("center-two-private-active-edge-relation"),
                DeclarationHandle.Create(Module + ".closed_single_active_edge_relation"),
                H("A two-coordinate square relates the normalized residual values"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At two active private coordinates the closed residual equation "
                    + "reduces to two terms. Negative Huang square curvature makes "
                    + "their base-edge-normalized single-coordinate values equal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("center-three-private-active-curvature"),
                DeclarationHandle.Create(Module + ".closed_triple_single_active_eq_zero"),
                H("Three closed single-active residuals cannot cancel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose one direction in each nonempty private block. For the "
                    + "three possible single-active rows, the closure relations "
                    + "and the pointwise sum force the normalized values to be pairwise "
                    + "opposite. They vanish, and the single-active support exhausts "
                    + "all remaining rows."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "CenterOutwardDifference")),
            DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "CenterOutwardWeightGauge"))
        ]));
}
