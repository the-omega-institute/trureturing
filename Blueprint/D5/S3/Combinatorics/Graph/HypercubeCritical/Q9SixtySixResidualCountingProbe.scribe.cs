using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class Q9SixtySixResidualCountingProbeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9SixtySixResidualCountingProbe", H("Q9SixtySixResidualCountingProbe"),
        Blocks(
            Paragraph(Text("Bound crossing incidences from each ball and from the residual graph."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/Q9SixtySixResidualMatchingProbe"))
        ]));
}
