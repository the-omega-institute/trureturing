using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport;

internal sealed class Q9SixtySixDistanceSumProbeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9SixtySixDistanceSumProbe", H("Q9SixtySixDistanceSumProbe"),
        Blocks(
            Paragraph(Text("The distance sum from a vertex is bounded by the count of its distance-seven partners. Summing by coordinates translates the bound into an inequality on the coordinate cut sizes."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtySixPointSupport/Q9SixtySixDiameterProbe"))
        ]));
}
