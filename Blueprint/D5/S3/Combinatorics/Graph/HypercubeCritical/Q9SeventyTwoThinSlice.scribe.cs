using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class Q9SeventyTwoThinSliceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9SeventyTwoThinSlice", H("Cubical geometry of a twenty-vertex half in the nine-cube"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9seventytwothinslice-structural-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/Q9SeventyTwoThinSlice.compressed_root_axes"),
                H("Cubical geometry of a twenty-vertex half in the nine-cube"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a 72-vertex Huang-balanced induced cubic support with a 20-vertex coordinate half, the half compresses to the cube or Wagner graph. A coordinate permutation fixing the cut puts the three paths from the root in one of five patterns. These are the starting configurations for classifying the actual embeddings in Hong–Wu–Xia’s Problem 2."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointCompression")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/Q9EightCubicGraphCertificate"))]));
}
