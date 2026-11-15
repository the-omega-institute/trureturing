using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class CubeTwelveSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/CubeTwelveSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Small supports of one cube parity with no singleton neighbor are complete nine-stars.",
        H("Single-parity supports of at most twelve vertices"),
        Blocks(
            Paragraph(Text(
                "This classification supplies the missing support obstruction in the four-edge-cut "
                    + "route toward Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2 "
                    + "(https://arxiv.org/html/2610.09483v1#Thmproblem2). "
                    + "The original question f₂(Q₉)=3 or 4 remains unresolved; "
                    + "this source claims neither literature novelty nor a classification of larger supports.")),
            Describe.Lean(
                DescribeId.Create("cube-twelve-support-nine-star"),
                DeclarationHandle.Create(Prefix + "eq_neighbors_of_card_le_twelve"),
                H("The support is a complete neighbor star"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be a nonempty subset of Q9 with at most twelve vertices. "
                            + "Assume every pair in S has even Hamming distance, and no cube vertex "
                            + "has exactly one neighbor in S. Then S is precisely the complete "
                            + "nine-vertex neighborhood of a cube vertex. The same-parity assumption "
                            + "is essential to the scope of this theorem.")),
                    Paragraph(Text(
                        "Every point of S has at least five points of S at distance two. "
                            + "A pair at distance six or eight forces disjoint five-point packs "
                            + "exhausting the remaining support. An outside direction then forces "
                            + "local coverage by at most six directions, contradicting nine. "
                            + "A distance-four pair instead forces two exclusive five-point packs. "
                            + "Their coordinate labels would inject five points into four coordinates: "
                            + "a repeated label and opposite-side coverage force a distance-six pair. "
                            + "All distinct points therefore have distance two, and the shared "
                            + "common-direction argument yields the complete star."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CubeNineSupport"))
        ]));
}
