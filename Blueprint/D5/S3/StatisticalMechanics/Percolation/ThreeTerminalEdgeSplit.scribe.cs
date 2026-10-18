using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalEdgeSplitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Percolation/ThreeTerminalEdgeSplit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Disjoint edge partitions and induced vertex restrictions preserve the entire "
            + "actual independent-edge three-terminal source.",
        H("Exact changes of actual edge coordinates"),
        Blocks(
            Node("edge_split_law", "Disjoint actual edge families", DescribeRole.Theorem,
                "For every finite decidable vertex type V, simple graphs H,K with finite "
                    + "decidable actual edge types and finite decidable union edge type, "
                    + "disjoint edge sets, terminals a,b,c in V and arbitrary real rates "
                    + "theta on (H union K).edgeSet, bondLaw(H union K) equals the actual "
                    + "endpoint law on H.edgeSet + K.edgeSet. Each side uses actualEdgeEnds "
                    + "and the restriction of theta along its edge inclusion. The edge-set "
                    + "union equivalence induces a bijection of complete Boolean cubes. "
                    + "The graph and all three path observations agree pointwise, the "
                    + "independent weights agree by product reindexing, and the finite "
                    + "pushforward sums agree by sum reindexing. Rates zero and one, "
                    + "negative formal rates, repeated terminals and empty sides are included."),
            Node("inducedEdgeEquiv", "The actual edges of a side", DescribeRole.Definition,
                "For every simple graph G and subset A of its vertex type, inducedEdgeEquiv "
                    + "is the bijection from (G.induce A).edgeSet to (sideGraph G A).edgeSet "
                    + "induced by forgetting the membership proofs of both endpoints. "
                    + "Every side edge has both endpoints in A, which supplies surjectivity."),
            Node("induced_source_law", "Restricting the vertex type", DescribeRole.Theorem,
                "For every finite decidable V, simple graph G, subset A with a finite "
                    + "decidable subtype, finite decidable actual edge types of G.induce A "
                    + "and sideGraph G A, terminals a,b,c in A and arbitrary real side "
                    + "edge rates theta, bondLaw(sideGraph G A) at their underlying "
                    + "vertices equals bondLaw(G.induce A) with rates theta composed "
                    + "with inducedEdgeEquiv. The complete source is retained: edge "
                    + "coordinates are bijective, arbitrary chosen edge orientations "
                    + "represent the same unordered edges, and the open side graph has "
                    + "no edges outside A. Its paths between vertices in A therefore "
                    + "correspond to paths in the induced open graph. A retraction to "
                    + "A, fixed on all actual side endpoints, gives the converse path "
                    + "map. The result preserves all five partition probabilities "
                    + "simultaneously, including deterministic rates and coincident labels.")),
        []));

    private static DocumentBlock Node(string name, string title, DescribeRole role, string text) =>
        Describe.Lean(DescribeId.Create("three-terminal-edge-split-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
}
