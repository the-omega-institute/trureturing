using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SymmetricTwentyFourExclusionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric Twenty Four Exclusion", H("Symmetric Twenty Four Exclusion"),
        Blocks(
            Paragraph(Text("Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, section 7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2), ask whether f2(Q9) is three or four. The external problem remains open; this result excludes the full symmetric (12,12;4,4) cube-slice branch in arbitrary finite cube dimension.")),
            Paragraph(Text("The claim is genuine: it quantifies an actual finite simple graph on Fin m, actual bipartition sides L and R of size twelve, exactly four degree-two vertices on each side, every vertex of degree two or three, independent degree-two vertices, extended girth at least eight, and an injective induced embedding into an arbitrary Boolean cube. It assumes no global distance-layer certificate, high-graph regularity, cycle labels, matching, or scalar certificate.")),
            Paragraph(Text("For every root, positive degree and the actual bipartition place the root on one side, possibly after swapping the two sides. The completed CubeLayerDisjointness result then derives the actual global neighborhood-disjointness property D from the induced cube embedding. The completed TwentyFourLayerRegularity result applies D to force every degree-three vertex to have exactly two degree-three neighbors.")),
            Paragraph(Text("The induced graph on the sixteen actual degree-three vertices is finite, has degree two at every vertex, inherits girth at least eight, and inherits the actual bipartition. The private two-regular decomposition therefore gives either one spanning induced C16 or two disjoint induced C8 components covering all high vertices with no cross high edge. The completed SixteenCycleExclusion and TwoEightCycleExclusion results refute these two actual branches after lifting their embeddings through the high-vertex subtype.")),
            Paragraph(Text("This settles the stated symmetric twenty-four-vertex exclusion only. It does not claim component size at least fifty-four, the full 258 exclusion, or a resolution of f2(Q9); those require further reductions.")),
            Describe.Lean(
                DescribeId.Create("symmetric-twenty-four-exclusion-claim"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyFourExclusion.claim"),
                H("claim"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exist an actual finite bipartite graph with sides of size twelve, four independent degree-two vertices on each side, all degrees two or three, extended girth at least eight, and an injective adjacency-reflecting Boolean-cube embedding."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("symmetric-twenty-four-exclusion-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyFourExclusion.result"),
                H("result"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The theorem has literally type Not claim. It derives D from the actual cube embedding, derives high-neighbor regularity, decomposes the actual sixteen-vertex high graph, and applies the two completed branch exclusions."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/CubeLayerDisjointness")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyFourLayerRegularity")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixteenCycleExclusion")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwoEightCycleExclusion")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighGraph"))
        ]));
}
