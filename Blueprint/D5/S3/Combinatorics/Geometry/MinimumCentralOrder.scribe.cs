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
            Describe.Lean(DescribeId.Create("minimum-central-order-result"),
                DeclarationHandle.Create(Prefix + "minimum_order"),
                H("The minimum orders"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For k ≥ 1, the least order of a nonempty finite metric space with exactly k "
                    + "central values is 1 when k=1, k when k is even, and k+1 when k ≥ 3 is odd. "
                    + "The edge-cover bound (k−1)⌈n/2⌉ against the n(n−1)/2 pairs of n points "
                    + "gives k ≤ n, and k ≤ n−1 when n ≥ 3 is odd, so an odd k needs at least "
                    + "k+1 points. For k ≥ 2 the round-robin band on 2m+2 points, "
                    + "m=⌊(k−1)/2⌋, with its first k−1 classes central and every other pair at "
                    + "its own distance has k central values, and one point serves for k=1. "
                    + "This is Corollary 6 of "
                    + "H. Ma and W. Zhang, answering Problem 4.3 of O. Dovgoshey and "
                    + "O. Rovenska."))),
                DescribeRole.Theorem))));
}
