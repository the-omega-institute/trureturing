using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9MixedBoundaryCollisionsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MixedBoundaryCollisions.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Collisions between edge translations from two components",
        H("Collisions between edge translations from two components"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-mixed-boundary-translation-count"),
                DeclarationHandle.Create(Prefix + "sum_mixed_multiplicity"),
                H("Mixed collisions count pairs at distance two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let C and D be disjoint vertex sets with no edge between them. For an exterior "
                        + "edge e, let m_C(e) and m_D(e) count coordinate flips carrying e to an "
                        + "internal edge of C and D, respectively. The sum of m_C(e)m_D(e) equals "
                        + "the number of triples (c,d,t) in which c ∈ C and d ∈ D have Hamming "
                        + "distance two and both have an internal edge in direction t. "
                        + "Distinguishing an endpoint of e produces two choices for each pair of "
                        + "flips. On the distance-two side, the same data distinguish one of the "
                        + "two common neighbors of c and d. The factors of two cancel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-mixed-boundary-258-collision-bound"),
                DeclarationHandle.Create(Prefix + "mixed_collision_bound"),
                H("A necessary collision count at 258 vertices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If C and D are closed Huang-balanced induced cubic components of a "
                        + "258-vertex subcubic U, their union has 6(|C|+|D|) boundary-edge "
                        + "translations counted with multiplicity. The complement of U contains "
                        + "at most 369 edges. For each exterior edge, expanding the second "
                        + "binomial moment of m_C+m_D gives the two within-component counts "
                        + "and the mixed product. Their sum is therefore at least "
                        + "6(|C|+|D|)−369."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This condition concerns the 258-vertex formulation of Hong–Wu–Xia, "
                    + "arXiv:2610.09483v1, §7 Problem 2 "
                    + "(https://arxiv.org/html/2610.09483v1#Thmproblem2). The value of f₂(Q₉) remains open."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BoundaryEdgeTranslations"))
        ]));
}
