using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SymmetricMixedExclusionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric Mixed Exclusion", H("Symmetric Mixed Exclusion"),
        Blocks(
            Paragraph(Text("The actual mixed high profiles force a closed Y and a disjoint high eight-cycle. The eight cycle lows exhaust all actual lows; a Y leaf meets an antipodal low pair and its adjacent arm meets a cycle low of opposite parity. The corresponding actual nonbacktracking three-walks force a high vertex to be low, contradicting its degree. Swapping the bipartition excludes B/A. No cube assumption is required for these mixed branches.")),
            Paragraph(Text("This module contributes to the live proof path of SymmetricSliceExclusion.result. Private helper declarations are proof organization and carry no independent novelty claim."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricMixedCycle")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricActualHighProfiles")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricCycleLowSaturation")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricLowPairDeficit"))
        ]));
}
