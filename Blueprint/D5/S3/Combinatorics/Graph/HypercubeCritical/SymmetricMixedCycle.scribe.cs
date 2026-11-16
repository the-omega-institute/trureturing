using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SymmetricMixedCycleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric Mixed Cycle", H("Symmetric Mixed Cycle"),
        Blocks(
            Paragraph(Text("The closed six-point mixed Y exhausts all exceptional high vertices. Its actual eight-point complement has full high degree two and girth at least eight; cycle extraction yields a genuine eight-cycle avoiding the arm and its leaf.")),
            Paragraph(Text("This module contributes to the live proof path of SymmetricSliceExclusion.result. Private helper declarations are proof organization and carry no independent novelty claim."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricMixedCore")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SmallRegularCycle"))
        ]));
}
