using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport;

internal sealed class Q9SixtyThinHalfProbeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9SixtyThinHalfProbe", H("Q9SixtyThinHalfProbe"),
        Blocks(
            Paragraph(Text("Use the existing small slice obstructions to show that each coordinate half of a sixty-vertex balanced cubic support has at least twenty-two vertices. Summing coordinate cut sizes gives the lower bound on the ordered distance sum."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SixtyShellCompositionProbe")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSlice"))
        ]));
}
