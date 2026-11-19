using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.SeventyTwoPointSupport;

internal sealed class ThinSliceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ThinSlice", H("Degree classes in a twenty-vertex coordinate half"),
        Blocks(
            Paragraph(Text("This case arises in Hong–Wu–Xia's Problem 2 on the nine-dimensional cube. A balanced cubic support of order 72 has 12 edges in each direction. When a coordinate half has 20 selected vertices, its internal edges exhaust the incidences between its 12 cut endpoints and its eight degree-three vertices.")),
            Describe.Lean(
                DescribeId.Create("q9-seventy-two-thin-slice-degree-classes"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SeventyTwoPointSupport/ThinSlice.degree_classes"),
                H("Every edge joins the two degree classes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each edge is incident to one degree-two vertex and one degree-three vertex. This permits the degree-two vertices to be suppressed when classifying the half."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeLowerBound")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/EighteenPointSlice"))
        ]));
}
