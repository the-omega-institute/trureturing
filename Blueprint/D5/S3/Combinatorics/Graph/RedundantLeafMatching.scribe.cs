using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class RedundantLeafMatchingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/RedundantLeafMatching.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two distinct leaves with the same neighbor are redundant for the cardinalities of maximal edge matchings. Folding one leaf onto the other gives a maximal matching of the actual induced residual with the same size. Inclusion of that residual lifts every maximal matching with the same size.",
        H("Redundant leaves and maximal matchings"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("edge-matching"),
                DeclarationHandle.Create(Prefix + "IsEdgeMatching"),
                H("Finite edge matchings"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite set M of unordered vertex pairs is an edge matching of G when every pair is an actual edge of G and any two distinct pairs in M have no common vertex. This is the IsEdgeMatching convention of the Formal Conjectures Authors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("maximal-edge-matching"),
                DeclarationHandle.Create(Prefix + "IsMaximalEdgeMatching"),
                H("Inclusion maximality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An edge matching M is maximal when no edge of G outside M can be inserted while preserving the matching property. Maximality is with respect to inclusion; it imposes no maximum-cardinality condition. This is the IsMaximalEdgeMatching convention of the Formal Conjectures Authors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("redundant-leaf-maximal-matching-transport"),
                DeclarationHandle.Create(Prefix + "redundant_leaf_maximal_matching_transport"),
                H("Transport in both directions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every universe, finite vertex type V with decidable equality, and simple graph G with decidable adjacency, let u,v,a be vertices. Assume u and v are distinct, each has degree one in G, and both are adjacent to a. No connectedness or degree bound is required. Set W={x : V | x is not u}, regarded as a subtype, and H=G.induce(W). Thus H uses the actual surviving vertices and their original adjacencies.")),
                    Paragraph(Text("Define f:V to W by sending u to the retained vertex v and every other vertex x to its own subtype representative. For every maximal edge matching M of G, let R(M) be the finite-set image of M under Sym2.map(f). Then R(M) is an actual maximal edge matching of H and its cardinality equals the cardinality of M. Conversely, for every maximal edge matching N of H, let L(N) be its image under Sym2.map(Subtype.val). Then L(N) is an actual maximal edge matching of G and its cardinality equals the cardinality of N.")),
                    Paragraph(Text("A maximal matching meets every ambient edge at some endpoint. The only possible collision under f identifies u and v. Edges incident to either leaf also contain a; two such edges cannot be distinct members of one matching. The edge map is therefore injective on M, and distinct image edges remain disjoint. Every residual edge meets the image matching because its endpoints are retained.")),
                    Paragraph(Text("For the converse, a maximal matching of H saturates a. The surviving edge va must meet the matching; if it meets at v, the matching edge at this leaf also contains a. Inclusion preserves matching disjointness and cardinality. It blocks all retained edges by maximality in H and blocks the restored edge ua at a.")),
                    Paragraph(Text("The transport is not a bijection between maximal matchings. For the three-vertex star with center a and leaves u,v, the two maximal matchings {au} and {av} have the same folded image {av}. Both cardinality-preserving directions hold."))),
                DescribeRole.Theorem)),
        []));
}
