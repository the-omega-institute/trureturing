using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MinimumCentralOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MinimumCentralOrder.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/mazhang2026centraledges");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least order of a nonempty finite metric space with exactly k central values is 1 "
            + "for k=1, k for even k and k+1 for odd k ≥ 3.",
        H("Minimum order of a k-central metric space"),
        Blocks(
            Describe.Lean(DescribeId.Create("minimum-central-order-capped"),
                DeclarationHandle.Create(Prefix + "Capped"),
                H("The capped round-robin space"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Capped m c is the point set {0,…,2m+1} with the round-robin classes of the "
                    + "parity construction. Distinct points in class r are at distance "
                    + "1+min(r,c)/(2m+2), a value in [1,2), so the triangle inequality holds. "
                    + "Every class is a perfect matching, so for c<2m+1 the central values are 0 "
                    + "and 1+r/(2m+2) for r ≤ c, which makes c+2 of them."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("minimum-central-order-result"),
                DeclarationHandle.Create(Prefix + "minimum_order"),
                H("The minimum orders"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For k ≥ 1, the least order of a nonempty finite metric space with exactly k "
                    + "central values is 1 when k=1, k when k is even, and k+1 when k ≥ 3 is odd. "
                    + "Every central value is a distance to a fixed point, so there are at most as "
                    + "many central values as points. If the two counts agree, the distances to "
                    + "each point are exactly the central values, so the central graph is "
                    + "complete and the parity classification forces the order to be 1 or even. "
                    + "Capped m c with m=⌊(k−1)/2⌋ and c=k−2 has 2m+2 points and k central "
                    + "values for k ≥ 2, and one point serves for k=1. This is Corollary 6 of "
                    + "H. Ma and W. Zhang, answering Problem 4.3 of O. Dovgoshey and "
                    + "O. Rovenska."))),
                DescribeRole.Theorem))));
}
