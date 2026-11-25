using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class CenterOutwardWeightGaugeDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardWeightGauge";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weight transport and separation of centered outward images",
        H("Weight transport and separation of centered outward images"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("center-outward-monomial-intertwining"),
                DeclarationHandle.Create(Module + ".outward_monomial_mul"),
                H("Coordinate weights act by the center monomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At a vertex the center monomial is the product of weights on the "
                    + "coordinates separating it from the center. An outward flip adds "
                    + "one such factor. Multiplication by the monomial intertwines the "
                    + "unit-weight and weighted outward differentials. When each weight "
                    + "is nonzero, the diagonal inverse gives a linear equivalence of "
                    + "the two kernels restricted to the same column support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("center-outward-closed-pair-separation"),
                DeclarationHandle.Create(Module + ".closed_pair_eq_zero"),
                H("Closed residuals at positive weighted distance cannot cancel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two opposite closed residuals would lie in the intersection of "
                    + "both outward kernels. The exact difference-energy identity forces "
                    + "their common vector to vanish if the weighted squared center distance "
                    + "is positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("center-outward-two-piece-weighted-kernel"),
                DeclarationHandle.Create(Module + ".weighted_pair_eq_zero"),
                H("Single-center injectivity extends to the weighted two-center sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every outward image is closed under its own differential. "
                        + "Distinct centers and nonzero coordinate weights force two "
                        + "canceling images to vanish separately. The monomial diagonal "
                        + "equivalence transports unit-weight injectivity on each original "
                        + "column support into the weighted setting.")),
                    Paragraph(Text(
                        "This algebraic implication prepares the actual paired-fibre "
                        + "boundary analysis for Hong, Wu and Xia's Problem 2. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardDifference")),
        ]));
}
