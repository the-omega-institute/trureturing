using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SingleTripleFiveCubeDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/SingleTripleFiveCube";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common degree-three direction set forces an eleven-vertex support in the balanced five-cube at eigenvalue square root of five.",
        H("Rigidity in a five-cube with a common direction triple"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("single-triple-five-cube-eleven-vertex-normal-form"),
                DeclarationHandle.Create(Module + ".eleven_vertex_normal_form"),
                H("Exact eleven-vertex support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let U be a finite subset of the five-cube with connected induced graph, "
                        + "balanced for the original Huang signing. Each selected vertex has at "
                        + "most three cube directions, and every vertex with three directions has "
                        + "the common set T. The unsigned adjacency rows admit a strictly positive "
                        + "eigenvector on U with eigenvalue square root of five.")),
                    Paragraph(Text(
                        "There are a vertex x and distinct complementary axes b and c such that "
                        + "y is obtained by flipping both b and c at x. Both x and y have "
                        + "direction set T. The support has eleven vertices and consists exactly "
                        + "of x, y, and the three internal vertices of the word i,b,c,i for "
                        + "each i in T. The same ordered pair b,c works for every i.")),
                    Paragraph(Text(
                        "Short signed cycles separate the degree-three vertices. Pairing the "
                        + "positive eigenvector with weights three, square root of five, and two "
                        + "forces equality in every local row bound. The resulting four-edge "
                        + "paths share endpoints by the three-axis square exclusion. Switching "
                        + "and anticommutation fix the common order, and connectedness propagates "
                        + "the resulting support. This classifies one component case relevant to "
                        + "Hong, Wu and Xia, arXiv:2610.09483v1, Section 7, Problem 2."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointEightWord"))
        ]));
}
