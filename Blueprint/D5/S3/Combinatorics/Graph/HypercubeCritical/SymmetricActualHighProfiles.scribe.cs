using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SymmetricActualHighProfilesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric Actual High Profiles", H("Symmetric Actual High Profiles"),
        Blocks(
            Paragraph(Text("Transfer the side profiles and saturation inequalities to the graph actually induced by degree-three vertices. The original eleven/eleven and four/four parameters give fourteen high vertices; opposite-side type B forces the relevant neighbor-sum equality.")),
            Paragraph(Text("This module contributes to the live proof path of SymmetricSliceExclusion.result. Private helper declarations are proof organization and carry no independent novelty claim."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighGraph")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighProfiles"))
        ]));
}
