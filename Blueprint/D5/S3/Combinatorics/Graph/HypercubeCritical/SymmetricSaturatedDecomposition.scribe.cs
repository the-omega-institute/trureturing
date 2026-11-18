using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SymmetricSaturatedDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric Saturated Decomposition", H("Symmetric Saturated Decomposition"),
        Blocks(
            Paragraph(Text("The exact B/B double-star is closed. Its eight-point complement has full high degree two and girth at least eight, yielding the actual induced eight-cycle and complete degree-two coverage.")),
            Paragraph(Text("This module contributes to the live proof path of SymmetricSliceExclusion.result. Private helper declarations are proof organization and carry no independent novelty claim."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSaturatedCore")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SmallRegularCycle"))
        ]));
}
