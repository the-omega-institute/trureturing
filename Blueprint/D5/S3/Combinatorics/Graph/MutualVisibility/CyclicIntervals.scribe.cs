using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MutualVisibility;

internal sealed class CyclicIntervalsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Auxiliary finite cut-counting structure for mutual-visibility reconfiguration.",
        H("CyclicIntervals"),
        Blocks(Paragraph(Text("Proper nonempty cyclic intervals have a unique initial vertex: it is selected and its predecessor is not. Their distinct starts supply disjoint deletion chains. The finite-index implementation transports these intervals through an injective labeling of an arbitrary selected set.")))));
}
