using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9BoundaryEdgeTranslationsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boundary-edge translations in the nine-cube",
        H("Boundary-edge translations in the nine-cube"),
        Blocks(
            Paragraph(Text(
                "Let C be a Huang-balanced induced cubic vertex set in Q₉, and let B be its "
                    + "exterior vertex boundary. Represent an edge of direction t by its endpoint "
                    + "whose t-bit is zero. The coordinate flip τᵢ toggles bit i at both endpoints. "
                    + "For i ≠ t it commutes with τₜ and preserves the t-bit, so the image is "
                    + "again an edge of direction t with the same endpoint convention.")),
            Describe.Lean(
                DescribeId.Create("q9-boundary-four-transverse-axes"),
                DeclarationHandle.Create(Prefix + "card_transverseExterior"),
                H("Four exterior translations per internal edge"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each endpoint of an internal edge has two other internal directions. "
                        + "These pairs are disjoint because a direction shared by both endpoints "
                        + "would give a square in C, which Huang balance forbids. Of the eight "
                        + "transverse axes, the four remaining flips send both endpoints into B."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-boundary-translation-count"),
                DeclarationHandle.Create(Prefix + "card_witnesses"),
                H("The total number of translations with multiplicity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The 3|C| oriented incidences count each internal edge twice. "
                        + "Pairing each internal edge with its four exterior axes gives 6|C| "
                        + "edge–axis pairs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-boundary-translated-edge-containment"),
                DeclarationHandle.Create(Prefix + "translatedEdges_subset_boundaryEdges"),
                H("Translated images lie in the induced boundary"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Write D for the distinct translated edges. Each image endpoint is outside C "
                        + "and adjacent to its original endpoint in C, so D ⊆ E(B). "
                        + "This containment holds for any C."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-boundary-distinct-edge-bound"),
                DeclarationHandle.Create(Prefix + "distinct_edge_bound"),
                H("A cut bound for distinct images"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose C ⊆ U, there are no edges from C to U ∖ C, and the induced graph "
                        + "on U has maximum degree at most three. Let T = Q₉ ∖ U and let q count "
                        + "the edges across the cut. Then B ⊆ T, 6|U| ≤ q, and "
                        + "q + 2|E(T)| = 9(512 − |U|). Since D ⊆ E(T), "
                        + "15|U| + 2|D| ≤ 4608. Cubicity and balance of C are unnecessary "
                        + "for this bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-boundary-sum-of-multiplicities"),
                DeclarationHandle.Create(Prefix + "sum_multiplicity"),
                H("The sum of boundary-edge multiplicities"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For e ∈ E(B), let mₑ count the edge–axis pairs with image e. "
                        + "For a Huang-balanced induced cubic C, the sum of mₑ over E(B) is 6|C|."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-boundary-collision-bound"),
                DeclarationHandle.Create(Prefix + "boundary_edge_bound"),
                H("A cut bound in terms of collisions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the balanced cubic and cut hypotheses, let Λ be the sum of "
                        + "binom(mₑ, 2) over E(B), counting unordered pairs with the same image. "
                        + "Summing mₑ ≤ 1 + binom(mₑ, 2) over D gives 6|C| ≤ |D| + Λ. "
                        + "The cut bound then gives 15|U| + 12|C| ≤ 4608 + 2Λ."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-boundary-seventy-two-collision-bound"),
                DeclarationHandle.Create(Prefix + "collisionCount_ge_63"),
                H("At least 63 collisions for a 72-vertex set"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If |C| = 72 and |U| ≥ 258 under the same hypotheses, then Λ ≥ 63."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The value of f₂(Q₉) remains open. Hong–Wu–Xia ask whether it is 3 or 4 "
                    + "in arXiv:2610.09483v1, §7 Problem 2 "
                    + "(https://arxiv.org/html/2610.09483v1#Thmproblem2)."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary"))
        ]));
}
