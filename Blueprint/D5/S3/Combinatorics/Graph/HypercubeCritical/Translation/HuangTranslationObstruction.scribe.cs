using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.Translation;

internal sealed class HuangTranslationObstructionDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/HuangTranslationObstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A translation stabilizing a Huang-balanced cube component has weight zero or one modulo four.",
        H("Translation periods of Huang-balanced cube components"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("huang-translation-even-choose-two"),
                DeclarationHandle.Create(Module + ".even_choose_two_of_reachable_translation"),
                H("Reachability of a translate forces even quadratic weight"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let C be a finite support in the Boolean n-cube, balanced for Huang's "
                        + "actual signed adjacency matrix. Let Tₐ act by coordinatewise XOR with a "
                        + "and send every vertex of C back into C. Suppose a walk in the cube "
                        + "graph induced on C joins x to Tₐx. Then the number of unordered pairs of "
                        + "TRUE coordinates in a is even. Equivalently the Hamming weight of a "
                        + "is zero or one modulo four.")),
                    Paragraph(Text(
                        "The diagonal factor D(a,x) contributes −1 for each ordered index pair "
                        + "j < i with a(j) and x(i) TRUE. The FALSE-prefix formula for Huang's "
                        + "matrix makes the product of the original and translated edge signs "
                        + "equal to the product of the two endpoint diagonal factors. For a "
                        + "switching σ on C, the value D(a,x)σ(x)σ(Tₐx) is therefore constant along "
                        + "the walk. Multiplying its values at x and Tₐx shows that "
                        + "D(a,x)D(a,Tₐx) equals one. In this product the factors that survive "
                        + "correspond precisely to pairs of TRUE coordinates of a.")),
                    Paragraph(Text(
                        "Reachability is necessary. The two antipodes 00 and 11 in Q₂ form a "
                        + "balanced support because there are no induced edges. The weight-two "
                        + "translation swaps them, with no walk between them in the support, "
                        + "and choose(2,2) = 1 is odd.")),
                    Paragraph(Text(
                        "For a connected cubic support C in Q9, each vertex has a full triple "
                        + "of incident directions. The translation period group acts freely on "
                        + "the vertices of each triple because XOR has no fixed vertices for "
                        + "a nonzero mask and commutes with every coordinate flip. Each realized "
                        + "triple therefore contributes at least one orbit of size equal to the "
                        + "group order. The number of triples times the group order is at most "
                        + "the size of C. If separate evidence supplies at least 22 distinct triples "
                        + "and C has at most 129 vertices, the group order is at most 4, since it "
                        + "is a power of two and 22 times 8 exceeds 129. This conditional counting "
                        + "argument concerns the cubic supports relevant to Hong, Wu and Xia, "
                        + "Graph Sensitivity of Cartesian Products with Matched Bridges, "
                        + "arXiv:2610.09483v1, Section 7 Problem 2, which asks whether f₂(Q₉) is "
                        + "3 or 4. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/GrayGridComponent")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum"))
        ]));
}
