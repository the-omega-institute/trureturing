using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SymmetricCycleLowSaturationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric Cycle Low Saturation", H("Symmetric Cycle Low Saturation"),
        Blocks(
            Paragraph(Text("Choose the actual unique low neighbors of eight cycle points with full graph degree three and high-graph degree two. They are distinct and exhaust all eight actual lows. Individual high leaves have antipodal low neighbors. The stronger all-degree-two-on-cycle statements are used only for B/B, where their coverage premise is proved; the mixed branch uses the generic exhaustion and individual-leaf statements.")),
            Paragraph(Text("This module contributes to the live proof path of SymmetricSliceExclusion.result. Private helper declarations are proof organization and carry no independent novelty claim."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricCycleLowPairs")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricLowPartners")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighGraph")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSaturatedDecomposition"))
        ]));
}
