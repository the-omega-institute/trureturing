using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9Gray54ExtensionBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9Gray54ExtensionBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single Gray54 bounds subcubic extensions in the nine-cube",
        H("The Gray54 extension bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-gray-fifty-four-extension-card"),
                DeclarationHandle.Create(Prefix + "card_le_of_balanced_cubic_fifty_four"),
                H("A subcubic extension has at most 257 vertices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let U be a vertex set of the nine-cube with induced maximum degree at most "
                        + "three. Suppose C ⊆ U has 54 vertices, is Huang-balanced and induced "
                        + "cubic, and contains every neighbor in U of each vertex of C. "
                        + "Reconstruction gives a partition into three triples and a center. "
                        + "Permuting coordinates and translating the center to the origin preserve "
                        + "Hamming distances and put C in the standard placement. In little-endian "
                        + "bit coordinates, the image of U ∖ C lies in the residual outside the "
                        + "closed neighborhood of that placement. Its induced degree is at most "
                        + "three, so the residual certificate gives |U| ≤ 54 + 203 = 257."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For the residual bound, compare a selected set S with a reference set of "
                    + "203 vertices. Begin with charge 3888 times the difference of the two "
                    + "membership indicators at each vertex. Apply the 25 signed transfers under "
                    + "all 1296 permutations of blocks and coordinates within blocks. Each "
                    + "transfer moves equal and opposite amounts, conditional on changes of "
                    + "membership in the intersection of the endpoints’ closed neighborhoods. "
                    + "Thus the total is 3888(|S| − 203) and each final charge is local. "
                    + "The local checks for the 15 block-weight profiles give a total upper "
                    + "bound of 3672. Since 3672 < 3888, integrality gives |S| ≤ 203.")),
            Describe.Lean(
                DescribeId.Create("q9-candidate-excludes-gray-fifty-four"),
                DeclarationHandle.Create(Prefix + "card_ne_fifty_four_of_candidate"),
                H("A 258-vertex candidate excludes Gray54"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If U has 258 vertices and induced maximum degree at most three, no "
                        + "neighbor-closed subset of U that is Huang-balanced and induced cubic "
                        + "has order 54. This applies in particular to actual connected components."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-candidate-two-large-balanced-components"),
                DeclarationHandle.Create(Prefix + "exists_two_large_balanced_components"),
                H("Two actual balanced cubic components have order at least 72"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every 258-vertex candidate of induced maximum degree at most three has "
                        + "two distinct actual connected components that are Huang-balanced and "
                        + "induced cubic. The small-order exclusion gives order 54 or at least "
                        + "72 for each. The Gray54 extension bound leaves order at least 72 "
                        + "for both."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This is a necessary condition for a subcubic candidate in Hong–Wu–Xia’s "
                    + "question about f₂(Q₉), whose value remains open here. "
                    + "See arXiv:2610.09483v1, §7 Problem 2 "
                    + "(https://arxiv.org/html/2610.09483v1#Thmproblem2)."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/TwoBalancedComponents"))
        ]));
}
