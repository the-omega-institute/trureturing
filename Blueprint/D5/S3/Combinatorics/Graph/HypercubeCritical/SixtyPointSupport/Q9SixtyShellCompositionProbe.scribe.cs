using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport;

internal sealed class Q9SixtyShellCompositionProbeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9SixtyShellCompositionProbe", H("Q9SixtyShellCompositionProbe"),
        Blocks(
            Paragraph(Text("Count the layers of a sixty-vertex support with respect to each root, using cubic degree and the minimum distance between vertices of each parity."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/CubicFiftyFourReconstruction")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9FourthLeafSignProbe"))
        ]));
}
