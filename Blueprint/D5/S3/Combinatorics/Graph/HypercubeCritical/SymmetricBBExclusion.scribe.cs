using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SymmetricBBExclusionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric B B Exclusion", H("Symmetric B B Exclusion"),
        Blocks(
            Paragraph(Text("Extract the actual B/B double-star and high eight-cycle. The eight cycle lows exhaust all actual lows, and the remaining high-leaf fibers are antipodal. Distinct actual labels preserve all twenty-nine candidate edges; degree equality proves inducedness and transfers the candidate nonembedding theorem. The induced finite-cube premise is essential for this branch.")),
            Paragraph(Text("This module contributes to the live proof path of SymmetricSliceExclusion.result. Private helper declarations are proof organization and carry no independent novelty claim."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricActualHighProfiles")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricCycleLowSaturation")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoNonEmbedding")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion"))
        ]));
}
