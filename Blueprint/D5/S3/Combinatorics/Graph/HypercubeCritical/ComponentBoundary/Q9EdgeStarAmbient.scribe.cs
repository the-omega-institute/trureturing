using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9EdgeStarAmbientDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EdgeStarAmbient";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite-parity four-face witnesses near a cubic edge",
        H("The five-face of a selected edge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-edge-opposite-mask-uniqueness"),
                DeclarationHandle.Create(Module + ".edge_has_at_most_one_opposite_mask"),
                H("At most one omitted axis can carry an opposite witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Choose an edge in a Huang-balanced support with degree three at each endpoint. "
                        + "Each endpoint supplies two transverse directions. A shared direction would "
                        + "give a selected square, so the main axis and the four distinct transverse axes "
                        + "span a five-face containing the edge and its four leaves.")),
                    Paragraph(Text(
                        "Take two subsets of a common subcubic support, each disjoint from and nonadjacent "
                        + "to the anchor support. In each subset, a witness is a four-face deficiency obtained "
                        + "by fixing one transverse coordinate. Its base vertex is even, agrees with the "
                        + "anchor outside the five active coordinates, and has parity opposite to the root "
                        + "after deleting the main coordinate. The theorem forces the two omitted axes to agree.")),
                    Paragraph(Text(
                        "The coordinates outside the five-face contribute the same parity at the base and "
                        + "the root. On the four transverse coordinates, the even base makes its parity equal "
                        + "to the sum of the column parity and the omitted bit. XOR by the root word sends "
                        + "the root to zero, shifts the omitted bit by its root bit, and shifts the column "
                        + "parity by the parity of the other three transverse root bits. Translation "
                        + "preserves paired columns, empty rows and their antipodal matching. The translated "
                        + "column parity and omitted bit therefore have odd sum.")),
                    Paragraph(Text(
                        "A witness in the zero slice would lie outside the closed neighborhood of the "
                        + "sliced anchor star. The four-face capacity bound leaves at most three such "
                        + "vertices, while a deficiency witness needs at least five. In the one slice, "
                        + "separation blocks one paired column and forces two empty rows. The deficiency "
                        + "cases then pair all three remaining columns and supply a selected endpoint in "
                        + "the transverse antipodal fiber. Each paired column gives both main-axis levels "
                        + "in one of the three transverse neighbor fibers.")),
                    Paragraph(Text(
                        "Two distinct omitted axes therefore give all four transverse neighbors at the same "
                        + "selected endpoint, even when the witnesses belong to different subsets. "
                        + "The rooted face embedding commutes with coordinate flips and assigns the four "
                        + "local directions to distinct ambient directions. That endpoint belongs to the "
                        + "common support, where its four neighbors contradict the degree bound."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The ambient theorem gives a conditional restriction on subcubic candidates for "
                + "Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9FourFaceDefect")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9ThreeAxisCapacityTransport"))
        ]));
}
