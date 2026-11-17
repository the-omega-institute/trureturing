using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class TwoEightCycleExclusionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two Eight Cycle Exclusion", H("Two Eight Cycle Exclusion"),
        Blocks(
            Paragraph(Text("Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, section 7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2), ask whether f2(Q9) is three or four. The external problem and its published results belong to that paper. This formal result excludes one high-cycle branch toward that question; it does not settle the original problem or claim literature priority.")),
            Paragraph(Text("The claim quantifies arbitrary finite vertex counts m and cube dimensions n, an actual simple graph G on Fin m, a bipartition L and R, and an injective map into the Boolean cube that preserves and reflects adjacency. Every vertex has full G-degree two or three, degree-two vertices form an independent set, and G has extended girth at least eight. Two injective, mutually disjoint maps u and v from Fin 8 label degree-three vertices and cover all degree-three vertices. Within each image adjacency is exactly the eight-cycle adjacency, and no high edge crosses between the two images. Neither a low matching, a pairing involution, nor an embedding of a prescribed twenty-four-vertex graph is assumed.")),
            Paragraph(Text("High coverage and exact high-cycle adjacency give exactly two high neighbors at every high vertex. The existing unique_low_partner theorem supplies its unique degree-two neighbor and that low vertex's distinct other high endpoint, together with its full two-element neighbor set. A shared low point forces equal bipartition colors on its endpoints. On one eight-cycle distinct vertices of equal color have cyclic separation two or four; the existing common-high and short-path lemmas exclude their resulting cycles of length four or six. Thus every top low partner lies on the bottom cycle. Uniqueness at bottom vertices proves injectivity of the resulting matching p.")),
            Paragraph(Text("Two rungs above a top edge cannot have adjacent bottom endpoints, because that would give distinct three-step paths with the same endpoints. Alternating bipartition colors then give distance at least three between p(i) and p(i+1), and distance at least two between p(i) and p(i+2). A finite three-point kernel computation and propagation classify p(i) as p(0)+3i or p(0)+5i modulo eight. Relabeling the bottom vertices as v(p(i)) turns their adjacency into steps three and five. The twenty-four actual vertices u(i), v(p(i)), and the selected low vertices are distinct and induce exactly the frozen SubdividedMobiusKantor graph: low neighbor saturation reflects every high-low adjacency, low independence excludes low-low edges, and the exact high-cycle hypotheses settle the remaining pairs. Composing this induced embedding with the original cube embedding contradicts SubdividedMobiusKantor.result.")),
            Paragraph(Text("The conclusion covers this exact two-disjoint-C8 high-graph branch in every finite cube dimension. It does not prove that all graphs with slice parameters (12,12;4,4) have this high graph. Other high graphs, their reduction from the external Q9 problem, and the value of f2(Q9) remain outside this result.")),
            Describe.Lean(
                DescribeId.Create("two-eight-cycle-exclusion-claim"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwoEightCycleExclusion.claim"),
                H("claim"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("There exist a finite bipartite graph, a genuine induced embedding into a finite Boolean cube, full degrees two or three, independent degree-two vertices, girth at least eight, and two disjoint induced eight-cycle labelings covering all degree-three vertices with no cross high edges."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("two-eight-cycle-exclusion-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwoEightCycleExclusion.result"),
                H("result"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The theorem has literally type Not claim. It derives the actual low matching and the induced twenty-four-vertex obstruction from the graph premises, then applies the existing cube nonembedding theorem."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricLowPartners")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SubdividedMobiusKantor"))
        ]));
}
