using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class CenterOutwardDifferenceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/CenterOutwardDifference";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted outward Huang differentials",
        H("Weighted outward Huang differentials"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("center-outward-difference-energy"),
                DeclarationHandle.Create(Module + ".outward_sub_energy"),
                H("Center distance determines difference energy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The centered outward differential retains the signed coordinate flips "
                    + "that increase distance from the center. Changing the center reverses the "
                    + "direction masks exactly on separating coordinates. Reindexing by a double "
                    + "flip cancels the mixed energy terms because of Huang square curvature. "
                    + "The resulting energy is the input energy times the sum of squared "
                    + "weights on the separating coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("center-outward-square-zero"),
                DeclarationHandle.Create(Module + ".outward_sq"),
                H("The outward differential squares to zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each restricted coordinate flip has square zero. Two different "
                    + "restricted flips anticommute. Their weighted sum therefore has square zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("closed-triple-center-energy"),
                DeclarationHandle.Create(Module + ".closed_triple_energy_relation"),
                H("Energy balance under three-center cancellation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Apply the first center's differential to three residuals that sum to "
                        + "zero and are each closed under their own differential. The two remaining "
                        + "images are opposite. The difference energy identity equates their "
                        + "energies with the two distances from the first center, measured "
                        + "by the squared coordinate weights.")),
                    Paragraph(Text(
                        "For unit weights the distances are Hamming distances. Cycling the "
                        + "argument relates all three energies to the opposite center distances. "
                        + "This provides an algebraic constraint for the paired-fibre approach "
                        + "to Hong, Wu and Xia's Problem 2. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum")),
        ]));
}
