using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class Q9SixtySixResidualHalfProbeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9SixtySixResidualHalfProbe", H("Q9SixtySixResidualHalfProbe"),
        Blocks(
            Paragraph(Text("Constrain the locations and degrees of the six residual vertices in the common-coordinate halves."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/Q9SixtySixResidualProbe"))
        ]));
}
