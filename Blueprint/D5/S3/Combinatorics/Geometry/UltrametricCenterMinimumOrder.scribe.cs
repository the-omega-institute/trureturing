using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class UltrametricCenterMinimumOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/UltrametricCenterMinimumOrder.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/dovgosheyrovenska2026ultrametriccenter");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite ultrametric space with k central distances has at least 2^(k−1) points, and every admissible set is realized at that order.",
        H("Minimum order of finite ultrametric spaces with a prescribed center"),
        Blocks(
            Describe.Lean(DescribeId.Create("ultrametric-center-lower-bound"),
                DeclarationHandle.Create(Prefix + "lower_bound"),
                H("At least 2^(k−1) points"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let C(X) be the center of distances of a metric space X: the set of t ≥ 0 such that "
                        + "every point of X has a point at distance t. Every finite ultrametric space with "
                        + "|C(X)| = k ≥ 1 has at least 2^(k−1) points, and for every k ≥ 1 some finite "
                        + "ultrametric space has |C(X)| = k and exactly 2^(k−1) points.")),
                    Paragraph(Text(
                        "Induct on the order. A space with |C(X)| ≥ 1 is nonempty, since the empty space has "
                        + "C = [0, ∞); a one-point space has C(X) = {0}. Otherwise let m > 0 be the diameter "
                        + "and p, q points with d(p, q) = m. The open m-balls around p and q are disjoint by "
                        + "the ultrametric inequality and are proper subsets. If t ∈ C(X) and t ≠ m then "
                        + "t < m, and a point at distance t from a point of the ball around p lies in that "
                        + "ball; so the center of each ball contains C(X) \\ {m}, of size at least k − 1. By "
                        + "induction each ball has at least 2^(k−2) points when k ≥ 2. Attainment uses the "
                        + "binary-word space of the next statement with A = {0, 1, …, k − 1}. This is "
                        + "Corollary 3.12 and Example 3.13 of O. Dovgoshey and O. Rovenska, arXiv:2603.25850."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ultrametric-center-realization"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Realizing a prescribed center at minimum order"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let A be a finite set of reals. The following are equivalent: A is the center C(X) "
                        + "of some finite ultrametric space; A is both the distance set D(X) and the center "
                        + "C(X) of some finite ultrametric space; 0 ∈ A and every element of A is nonnegative. "
                        + "For such A, 2^(|A|−1) is the least order of a finite ultrametric space with "
                        + "C(X) = A, and it is attained by a space with D(X) = C(X) = A.")),
                    Paragraph(Text(
                        "Necessity: an empty space has C = [0, ∞), which is not finite, so X is nonempty; then "
                        + "0 ∈ C(X) because every point is at distance 0 from itself, and C(X) ⊆ [0, ∞). "
                        + "Sufficiency: list A as "
                        + "0 = a₀ < a₁ < … < aₙ with n = |A| − 1, take the 2ⁿ binary words of length n, and "
                        + "let the distance of two different words be a_j, where j is one plus the highest "
                        + "position where they differ. Positions where u and w differ are positions where u, v "
                        + "or v, w differ, so this is an ultrametric. Flipping position j − 1 of any word "
                        + "gives a word at distance a_j, so every element of A occurs at every point and "
                        + "D(X) = C(X) = A. Minimality is the previous bound. This is Conjecture 4.4 of "
                        + "Dovgoshey and Rovenska (arXiv:2603.25850), proved as Proposition 4.5 and "
                        + "Corollary 4.6 of O. Dovgoshey, N. S. Jaiswal, S. P. S. Kainth, G. Kaur and "
                        + "O. Rovenska (arXiv:2609.11384); the explicit word metric replaces their labelled "
                        + "perfect binary tree."))),
                DescribeRole.Theorem))));
}
