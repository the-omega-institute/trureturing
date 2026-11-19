using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SymmetricLowPartnersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric Low Partners", H("Symmetric Low Partners"),
        Blocks(
            Paragraph(Text("A full-degree-three vertex with two actual high neighbors has one actual low neighbor, whose other endpoint is a uniquely determined distinct high vertex. The exact low neighborhood and uniqueness are derived from actual degrees and independent lows.")),
            Paragraph(Text("This module contributes to the live proof path of SymmetricSliceExclusion.result. Private helper declarations are proof organization and carry no independent novelty claim."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceLabels"))
        ]));
}
