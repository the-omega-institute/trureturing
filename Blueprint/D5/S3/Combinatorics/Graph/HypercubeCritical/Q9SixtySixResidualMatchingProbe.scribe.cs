using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class Q9SixtySixResidualMatchingProbeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9SixtySixResidualMatchingProbe", H("Q9SixtySixResidualMatchingProbe"),
        Blocks(
            Paragraph(Text("Charge isolated crossing incidences to the degree-two vertices of the residual graph."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/Q9SixtySixResidualHalfProbe"))
        ]));
}
