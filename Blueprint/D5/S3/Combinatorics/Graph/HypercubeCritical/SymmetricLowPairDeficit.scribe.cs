using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SymmetricLowPairDeficitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric Low Pair Deficit", H("Symmetric Low Pair Deficit"),
        Blocks(
            Paragraph(Text("Distinct actual highs sharing a low have disjoint relevant low-neighbor capacities. Combining the capacity with weighted high-neighbor counts gives a local deficit bound; four lows and two degree-two high points force zero deficit.")),
            Paragraph(Text("This module contributes to the live proof path of SymmetricSliceExclusion.result. Private helper declarations are proof organization and carry no independent novelty claim."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighProfiles")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceLabels"))
        ]));
}
