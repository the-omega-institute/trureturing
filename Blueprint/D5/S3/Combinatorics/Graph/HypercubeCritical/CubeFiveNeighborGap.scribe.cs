using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class CubeFiveNeighborGapDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/CubeFiveNeighborGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five actual support neighbors force at least sixteen support points for unit integer vectors whose original Huang rows are divisible by three.",
        H("Five support neighbors force sixteen points"),
        Blocks(
            Paragraph(Text(
                "Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2 "
                    + "(https://arxiv.org/html/2610.09483v1#Thmproblem2), asks whether "
                    + "f₂(Q₉)=3 or 4 (the 258-vertex question). The original external "
                    + "problem remains unresolved here; literature novelty is unconfirmed. "
                    + "Throughout, intA and intCoeff retain the original FALSE-prefix "
                    + "signed Huang integer operator and coefficients from HuangIntegralNormGap.")),
            Describe.Lean(
                DescribeId.Create("sixteen-le-support-card-of-neighbor-card-eq-five"),
                DeclarationHandle.Create(Prefix + "sixteen_le_support_card_of_neighbor_card_eq_five"),
                H("A row with five actual support neighbors forces support at least sixteen"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For q : Q9 → ℤ, assume hu: every q(x) is 0, 1, or −1, "
                            + "and hdiv: 3 divides intA q v for every v. Let "
                            + "S = {x : q(x) ≠ 0}. Given y : Q9 and hfive: "
                            + "|S ∩ N(y)| = 5, where N(y) is the actual cube "
                            + "neighborhood, the conclusion is 16 ≤ S.card. These "
                            + "are exactly the hypotheses of "
                            + "sixteen_le_support_card_of_neighbor_card_eq_five(q, hu, hdiv, y, hfive); "
                            + "there is no parity, eigenvector, or balanced-graph assumption.")),
                    Paragraph(Text(
                        "Suppose |S| ≤ 15. Let I be the five directions whose "
                            + "flips from y lie in S, and J the remaining four. "
                            + "The twenty distinct cross rows flip y in one I "
                            + "direction and one J direction. Each sees exactly "
                            + "one support point in N(y). A unit Huang row "
                            + "divisible by three cannot have just one support "
                            + "neighbor, so each cross row needs a neighbor in "
                            + "T = S ∖ N(y), with |T| ≤ 10. Any T point adjacent "
                            + "to a cross row has distance three from y. Its "
                            + "three differing coordinates give at most two "
                            + "I × J cross incidences. Double counting saturates "
                            + "all bounds: |T| = 10, each cross row has exactly "
                            + "one T neighbor, and each T point covers exactly two cross rows.")),
                    Paragraph(Text(
                        "If the two rows covered by a T point had different "
                            + "J coordinates, distance three forces their I "
                            + "coordinates to coincide. Each row then has exactly "
                            + "two actual support neighbors, so divisibility by "
                            + "three makes both original signed row sums zero. "
                            + "The original gamma anticommutation identity makes "
                            + "these two equations incompatible with nonzero "
                            + "unit values at their common support endpoints. "
                            + "Thus the two cross indices share their J coordinate; "
                            + "this uses the signed operator identity, without "
                            + "asserting balancedness of a chosen square.")),
                    Paragraph(Text(
                        "Fix any j ∈ J and let U ⊆ T be the points covering "
                            + "that J fiber. Its five rows each have one T "
                            + "neighbor, while every point of U covers exactly "
                            + "two rows in the fiber. Hence 5 = 2|U|, a "
                            + "contradiction."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangUnitSupportGap")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CubeTwelveSupport")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary"))
        ]));
}
