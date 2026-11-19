using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SymmetricMixedCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric Mixed Core", H("Symmetric Mixed Core"),
        Blocks(
            Paragraph(Text("One-sided saturation in the actual A/B high profiles forces a closed six-point Y: a degree-three center, its leaf, two degree-two arms, and their leaves. All six vertices are distinct and all exact neighbor sets are proved. No saturation on the other side is assumed.")),
            Paragraph(Text("This module contributes to the live proof path of SymmetricSliceExclusion.result. Private helper declarations are proof organization and carry no independent novelty claim."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/GirthSliceCounting"))
        ]));
}
