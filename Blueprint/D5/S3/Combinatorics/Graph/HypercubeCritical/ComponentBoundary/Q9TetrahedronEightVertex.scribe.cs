using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9TetrahedronEightVertexDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9TetrahedronEightVertex";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The eight-vertex obstruction for twelve capped tetrahedra",
        H("The eight-vertex obstruction for twelve capped tetrahedra"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-twelve-tetrahedra-eight-vertex-obstruction"),
                DeclarationHandle.Create(Module + ".tetrahedra_card_ne_twelve_on_eight_vertices"),
                H("Eight used vertices are impossible"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Twelve tetrahedra have forty-eight vertex incidences. "
                        + "On eight used vertices, the six-triangle lower bound "
                        + "therefore holds with equality in every link. Each link "
                        + "is a triangular bipyramid with five vertices and nine edges.")),
                    Paragraph(Text(
                        "Each vertex of the support graph has five neighbors, so its "
                        + "complement is 2-regular with eight edges. Removing a vertex "
                        + "and its two complement neighbors removes at most four of "
                        + "those edges. At most six support edges remain among the "
                        + "five original neighbors, contradicting the bipyramid.")),
                    Paragraph(Text(
                        "This rules out an eight-vertex twelve-facet support in the "
                        + "sharp contact-shell reduction of Hong, Wu and Xia's Problem 2. "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9CappedTriangleLinkFive")),
        ]));
}
