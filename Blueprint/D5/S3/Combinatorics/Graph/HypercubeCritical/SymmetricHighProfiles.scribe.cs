using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SymmetricHighProfilesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric High Profiles", H("Symmetric High Profiles"),
        Blocks(
            Paragraph(Text("Derive the actual high-neighbor square bound and the two possible side profiles A=(1,6,0) and B=(2,4,1). The weighted local deficit inequality records the opposite-side dependence; type B on one side forces saturation on the other.")),
            Paragraph(Text("This module contributes to the live proof path of SymmetricSliceExclusion.result. Private helper declarations are proof organization and carry no independent novelty claim."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighTypes")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoLocal"))
        ]));
}
