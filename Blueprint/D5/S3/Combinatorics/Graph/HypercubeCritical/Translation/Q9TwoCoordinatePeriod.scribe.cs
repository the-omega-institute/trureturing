using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.Translation;

internal sealed class Q9TwoCoordinatePeriodDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9TwoCoordinatePeriod";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A 258-point subcubic induced subgraph of Q9 has no two-coordinate translation period.",
        H("Two-coordinate periods in Q9"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-two-coordinate-period"),
                DeclarationHandle.Create(Module + ".not_two_coordinate_period"),
                H("Two distinct flips cannot preserve a 258-point subcubic support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let U be a set of 258 vertices in the Boolean 9-cube whose induced "
                        + "graph has maximum degree at most 3. For any distinct coordinates i "
                        + "and j, some vertex of U leaves U when both coordinates are flipped.")),
                    Paragraph(Text(
                        "For nonnegative coordinate weights w, let H be the weighted signed "
                        + "Huang operator. On the 258-point support U, extending by zero, "
                        + "applying H and restricting to the complement defines a linear map "
                        + "from dimension 258 to dimension 254. A nonzero kernel vector extends "
                        + "to a nonzero f with both f and Hf supported on U. If each selected "
                        + "vertex has total incident weight at most d, the unit absolute values "
                        + "of the edge signs bound Hf by d times the maximum absolute entry of f. "
                        + "Applying the bound to Hf at a maximizing vertex of f and using the "
                        + "weighted Huang square gives the inequality Σ w² ≤ d² from Daniel V. "
                        + "Mathews, The sensitivity conjecture, induced subgraphs of cubes, "
                        + "and Clifford algebras, Theorem 1.2. https://doi.org/10.4171/jems/1180")),
                    Paragraph(Text(
                        "Suppose flipping i and j preserves U. The two single-flip neighbors "
                        + "of any vertex are exchanged by the double flip, because the flips "
                        + "commute and each is an involution. Applying the period at each "
                        + "neighbor in U shows that the two directions occur together. "
                        + "Weights 0 at i, 2 at j and 1 elsewhere therefore give a weighted "
                        + "degree equal to the induced degree at each vertex of U. "
                        + "The squared weights sum to 11, contradicting the bound of 9."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SignedContactCells")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicHuang")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/SupportedEigenDimension"))
        ]));
}
