using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Products;

internal sealed class CarneroBravoKingRoutesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Products/CarneroBravoKingRoutes.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/carnerobravo2025independenceproducts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual prescribed subdivision and its induced finite king-grid embedding for the Question 32 route.",
        H("The 178-route induced king-grid certificate"), Blocks(
            Paragraph(Text("Carnero Bravo, arXiv:2505.06457v2 Question 32, asks whether the hereditary sphere-wedge statement for king grids of widths at most four extends to every width. An induced subgraph is the relevant target. Question 35 instead concerns the full grid. This module implements the embedding interface of the proposed Question 32 counterexample; it does not prove a homology obstruction or settle either question.")),
            Paragraph(Text("The original labels, edges, coordinates and 178 corner lists are literal scientific inputs. The seed belongs to Adamaszek's Small flag complexes with torsion, arXiv:1208.3892v1; the graph-move route follows the Barmak/Lozin approach. The explicit coordinate construction and its formal certificate are local. No independent original-problem or unique credit is claimed.")),
            Node("subdivision", "subdivision", "The actual prescribed subdivision",
                "Original is the subtype of the 141 retained natural labels, Edge is Fin 178, and the exact 178 route records specify the endpoints and k(e). Fresh vertices are tagged by their edge and an index in Fin (3 k(e)). The coordinate of an interior vertex is sample(corners(e),i+1), with every corner and detour retained.", DescribeRole.Definition),
            Node("polyline-data", "polyline_facts", "The complete finite route facts",
                "For every actual route, the corner list is nonempty and axis-aligned, its Manhattan length is 3 k(e)+1, and its samples at positions zero and 3 k(e)+1 equal the old endpoint coordinates. This is a kernel-reduction obligation over the literal data.", DescribeRole.Theorem),
            Node("path-enumeration", "path_coordinate_verifier", "Every path position has the verifier's coordinate",
                "For every e and every position i in Fin (3 k(e)+2), coordinate(pathVertex(e,i)) is exactly element i of verifierExpand(corners(e)), using the same optional-lookup default. The nonempty length and endpoint facts ensure the consumed path positions are valid. No Python output is a proof premise.", DescribeRole.Theorem),
            Node("endpoints", "endpoint_inventory", "Every original edge is represented",
                "The image of all route indices under the unordered endpoint-pair function equals the literal 178-edge construction inventory.", DescribeRole.Theorem),
            Node("endpoint-unique", "endpoint_pair_injective", "Distinct route indices have distinct endpoint pairs",
                "The endpoint-pair map from Edge to unordered pairs of original natural labels is injective. Together with the exact inventory this identifies the routes with the edges of the actual original simple graph.", DescribeRole.Theorem),
            Node("base-graph", "baseGraph_iff_endpoints", "Exact old-graph incidence",
                "For all a,b in Original, baseGraph.Adj(a,b) iff some route has endpoints (a,b) in one of the two orders. No replacement graph or assumed graph isomorphism occurs in this interface.", DescribeRole.Theorem),
            Node("routing-reduction", "routing_check_success", "The actual occupancy check",
                "routingCheck on RoutedGraph, its complete fresh-vertex and path-edge lists, and the actual coordinate function equals true. The obligation uses ordinary kernel reduction. It checks freshness and all four spatial neighbors of each occupied point; it does not enumerate every pair of the 93,999 vertices.", DescribeRole.Theorem),
            Node("exact-routing", "exact_square_routing", "Injection and both adjacency implications",
                "coordinate is injective and, for every pair of actual vertices, RoutedGraph adjacency is equivalent to Manhattan distance one between their coordinates. This is the soundness application consumed by the finite embedding.", DescribeRole.Theorem),
            Node("bounds", "actual_T_bounds", "The inclusive bounds of the literal transform",
                "For every actual vertex v, T(coordinate(v))=(x+y+25,x-y+1705) lies in [1,9337] times [1,9061]. Both coordinates are one-based and both are reduced by one when entering the Fin types.", DescribeRole.Theorem),
            Node("embedding", "inducedEmbedding", "The actual finite induced embedding",
                "inducedEmbedding maps RoutedGraph into the strong product of pathGraph 9337 and pathGraph 9061 on Fin 9337 times Fin 9061. Its coordinate map is (T_x-1,T_y-1). The strong product includes Mathlib boxProd edges and simultaneous factor adjacency, so it is the finite king grid. The map is injective and reflects as well as preserves every adjacency.", DescribeRole.Definition),
            Node("range-iso", "inducedIso", "Isomorphism onto the induced range",
                "selected is the actual set-theoretic range of inducedEmbedding. The pinned Mathlib isoInduceRange construction yields RoutedGraph isomorphic to rectangle.induce(selected). Thus the target is an induced subgraph of the stated finite rectangle.", DescribeRole.Definition),
            Node("sum-k", "sum_subdivisions", "The exact prescribed multiplicity sum",
                "The sum over the 178 actual k(e) is 31286. This is the number of triple subdivisions needed to form the prescribed paths after the separate graph-move stage.", DescribeRole.Theorem),
            Node("vertex-count", "actual_vertex_count", "Exactly 93,999 vertices",
                "RoutedGraph has 141 old vertices and 93858 fresh vertices, hence 93999 vertices. This follows from the general tagged-subdivision cardinality formula and the exact multiplicity data.", DescribeRole.Theorem),
            Node("edge-count", "actual_edge_count", "Exactly 94,036 edges",
                "The exact routed graph has 94036 edges, the sum of 3 k(e)+1 over all 178 routes. No quadratic vertex-pair enumeration is required for this count.", DescribeRole.Theorem),
            Paragraph(Text("Separate obligations remain: replay of the supplied 40 graph moves from the Adamaszek seed with the actual ambient edges, identification of prescribed subdivisions with genuine suspension moves, transport of the torsion class through those moves, finite-chain/singular-homology comparison, and the sphere-wedge torsion obstruction. The large routing certificate supplies none of those homology conclusions as an assumption.")))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
