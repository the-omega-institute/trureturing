using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport;

internal sealed class Q9SixtySixShellProbeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9SixtySixShellProbe", H("Q9SixtySixShellProbe"),
        Blocks(
            Paragraph(Text("Bound distance-six and distance-seven shells, and give a lower bound on each coordinate half of a 66-vertex balanced cubic support."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SixtyExclusionProbe"))
        ]));
}
