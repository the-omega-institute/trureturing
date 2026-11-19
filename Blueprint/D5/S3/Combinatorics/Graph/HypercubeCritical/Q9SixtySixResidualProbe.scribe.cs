using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class Q9SixtySixResidualProbeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9SixtySixResidualProbe", H("Q9SixtySixResidualProbe"),
        Blocks(
            Paragraph(Text("Describe the six vertices left outside the two disjoint radius-three balls of a putative distance-eight pair."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/Q9SixtySixShellProbe"))
        ]));
}
