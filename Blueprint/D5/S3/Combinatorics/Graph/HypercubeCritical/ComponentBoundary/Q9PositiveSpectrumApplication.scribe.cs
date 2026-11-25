using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9PositiveSpectrumApplicationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositiveSpectrumApplication";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Occupied spectra of actual paired fibres",
        H("Occupied spectra of actual paired fibres"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-component-adjacency"),
                DeclarationHandle.Create(Module + ".component_adjacency_eigenvalue"),
                H("Adjacency eigenvalue four"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complementary Huang Gram identity has scalar eight at unit transverse weights. The occupied Gram is four on the diagonal and the occupied adjacency off the diagonal. A boundary kernel therefore gives an adjacency eigenvector of eigenvalue four."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-positive-spectrum-bound"),
                DeclarationHandle.Create(Module + ".exists_two_components_with_positive_spectrum_bound"),
                H("Every axis in two actual components has at least nine paired fibres"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The positive eigenvector on a fixed occupied component invokes the spectral count and eight-star equality. If the actual axis had only eight paired fibres, they would all have the same projected parity, contradicting the exact occupied-fibre divisibility. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositivePairedKernel")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/DiamondFreeSpectral")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarRigidity")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PairedFibreAnyAxis"))]));
}
