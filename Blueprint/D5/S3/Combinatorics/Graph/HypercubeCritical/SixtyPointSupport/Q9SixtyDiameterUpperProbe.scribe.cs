using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport;

internal sealed class Q9SixtyDiameterUpperProbeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9SixtyDiameterUpperProbe", H("Q9SixtyDiameterUpperProbe"),
        Blocks(
            Paragraph(Text("Use opposite coordinate halves and the fourth-layer counting constraints to rule out distances eight and nine in a sixty-point support."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9SixtyThinHalfProbe"))
        ]));
}
