using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9MaskedFiveFaceDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedFiveFace";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An eleven-vertex normal form from a singular five-axis mask",
        H("The five-cube normal form on a masked face"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-eleven-vertex-masked-component"),
                DeclarationHandle.Create(Module + ".exists_eleven_vertex_masked_component"),
                H("A common full triple forces an ambient eleven-vertex normal form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take a balanced subcubic actual component and a singular mask of five axes. "
                        + "Suppose that every degree-three direction set contained in the mask equals T. "
                        + "Then the masked graph on that actual component has a connected component with "
                        + "eleven vertices. There are distinct ambient coordinates a and b such that "
                        + "removing T from the mask leaves exactly a and b. Two vertices x and y "
                        + "in the same masked component have full ambient direction set T, and y is "
                        + "obtained from x by flipping a and b. The support consists exactly of x, y, "
                        + "and, for each i in T, the vertices obtained by flipping i at x, by flipping "
                        + "i and then a at x, and by flipping i at y.")),
                    Paragraph(Text(
                        "The positive spectral component lies in one five-face because masked paths "
                        + "leave the other coordinates fixed. Relabel its active axes to identify that "
                        + "face with the five-cube. The two Huang signings both anticommute around "
                        + "coordinate squares, so their ratio is a flat signing and is removed by "
                        + "vertex switching. The coordinate identification preserves adjacency rows "
                        + "and active directions. Every masked degree-three vertex retains its full "
                        + "triple, so the eleven-vertex normal form applies. The face embedding "
                        + "commutes with each flip after relabeling its axis. This transports the "
                        + "endpoints and the entire support to the original nine coordinates.")),
                    Paragraph(Text(
                        "Universal Huang saturation supplies the singularity hypothesis at the mask "
                        + "weights. This gives a conditional restriction on the subcubic candidates in "
                        + "Hong, Wu and Xia's Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9MaskedSpectrum")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/SingleTripleFiveCube")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance"))
        ]));
}
