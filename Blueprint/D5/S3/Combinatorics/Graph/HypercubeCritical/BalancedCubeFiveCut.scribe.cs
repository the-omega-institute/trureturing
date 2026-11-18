using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class BalancedCubeFiveCutDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiveCut.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A five-edge cut with at least four vertices on each side in a connected balanced induced cubic Q9 graph requires at least sixty-six vertices.",
        H("Nontrivial five-edge cuts require sixty-six vertices"),
        Blocks(
            Paragraph(Text(
                "Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2 "
                    + "(https://arxiv.org/html/2610.09483v1#Thmproblem2), asks whether "
                    + "f₂(Q₉)=3 or 4. This excludes additional structures in the "
                    + "balanced cubic components associated with 258-vertex "
                    + "candidates. The original question remains unresolved, "
                    + "and literature novelty has not been established.")),
            Describe.Lean(
                DescribeId.Create("balanced-cube-five-cut-sixty-six-bound"),
                DeclarationHandle.Create(Prefix + "sixty_six_le_card_of_cut_card_eq_five"),
                H("An actual five-edge cut with two sides of size at least four forces sixty-six vertices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let C,T : Finset Q9. Assume the actual induced graph on C "
                            + "is regular of degree three and connected, the original "
                            + "FALSE-prefix IsBalanced C holds, T ⊆ C, the actual "
                            + "BalancedCubeCut.cutEdges C T has cardinality five, "
                            + "4 ≤ T.card, and 4 ≤ (C \\ T).card. Then 66 ≤ C.card. "
                            + "The bound is conditional on this actual five-edge "
                            + "cut and both side-size assumptions.")),
                    Paragraph(Text(
                        "Assume C.card < 66 and write L = 3I − A for the "
                            + "original integer Huang operator. Actual cut erasure "
                            + "and FourCut force the cut edges to form a matching. "
                            + "The partial switching vector f has energy five and "
                            + "|Lf| ≤ 1 on C. The full energy-five classification "
                            + "has a unit branch and a coherently signed P3 branch.")),
                    Paragraph(Text(
                        "In the P3 branch, the leaves lie outside C because their "
                            + "residual coefficients have magnitude two. If the "
                            + "center lay in C, the integer +3 eigenvectors f − g, "
                            + "total − f + g, and total would have squared norms "
                            + "whose difference is four or eight, contradicting "
                            + "divisibility by six. Thus the center is also outside C. "
                            + "The first two eigenvectors are nonzero and unit-valued. "
                            + "The consumed private helper in HuangUnitThirtyGap "
                            + "combines the thirty-point lower bound, exclusion of "
                            + "thirty after a parity sign change, and divisibility "
                            + "of integer eigennorms by six to give support at least thirty-six. "
                            + "Their support lower bounds of thirty-six force both sides "
                            + "to have at least 33 vertices, contradicting C.card < 66.")),
                    Paragraph(Text(
                        "The remaining branch gives a unit negative-three "
                            + "eigenvector Lf with support exactly thirty. "
                            + "HuangUnitThirtyGap excludes this branch by applying "
                            + "the five-neighbor bound to a fifteen-point parity "
                            + "part. Both classification branches are therefore "
                            + "excluded. This proves the stated actual-graph bound; "
                            + "it supplies no 258-point construction or complete "
                            + "exclusion, and does not prove the existence of a "
                            + "graph attaining sixty-six vertices."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangEnergyFiveResidual")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitNormThirty")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitThirtyGap"))
        ]));
}
