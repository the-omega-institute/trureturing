using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

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
                "For every e and every position i in Fin (3 k(e)+2), coordinate(pathVertex(e,i)) is exactly element i of verifierExpand(corners(e)). The index is proved to lie within the expanded route, so this statement uses actual element access. Old coordinates likewise use a proved-present table entry. No Python output is a proof premise.", DescribeRole.Theorem),
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
            Node("selected-vertices", "selected_vertex_count", "The induced range has 93,999 vertices",
                "The range isomorphism transfers the exact vertex cardinality to selected.", DescribeRole.Theorem),
            Node("selected-edges", "selected_edge_count", "The induced range has 94,036 edges",
                "The range isomorphism transfers the exact edge cardinality to rectangle.induce(selected).", DescribeRole.Theorem),
            Paragraph(Text("Separate obligations remain: replay of the supplied 40 graph moves from the Adamaszek seed with the actual ambient edges, identification of prescribed subdivisions with genuine suspension moves, transport of the torsion class through those moves, finite-chain/singular-homology comparison, and application of the sphere-wedge torsion obstruction. The large routing certificate supplies none of those homology conclusions as an assumption.")))));

    private static Formula Statement(string declaration)
    {
        var e = I("e"); var i = I("i"); var v = I("v"); var w = I("w");
        var a = I("a"); var b = I("b"); var d = C("subdivision");
        var edge = C("Edge"); var original = C("Original"); var vertex = C("Vertex");
        var route = C("route", e); var corners = C("corners", route);
        var k = C("k", d, e); var last = Add(Mul(D(3), k), D(1));
        var pairFunction = LambdaTerm("e", edge,
            C("SymPair", C("left", route), C("right", route)));
        var exactAdj = All("v", vertex, All("w", vertex,
            Bicond(C("Adj", C("RoutedGraph"), v, w),
                C("squareAdj", C("coordinate", v), C("coordinate", w)))));
        var routing = C("routingCheck", C("RoutedGraph"), C("vertices", d), C("edgePairs", d), C("coordinate"));
        var rv = C("rotate", C("coordinate", v));
        return declaration switch
        {
            "subdivision" => Seq(d, Colon, C("Data", original, edge)),
            "polyline_facts" => All("e", edge,
                And(new Formula.Not(Equal(corners, C("Nil"))), And(C("axisAligned", corners),
                And(Equal(C("length", corners), last),
                And(Equal(C("sample", corners, D(0)), C("oldCoordinate", C("left", d, e))),
                    Equal(C("sample", corners, last), C("oldCoordinate", C("right", d, e)))))))),
            "path_coordinate_verifier" => All("e", edge, All("i", C("Fin", Add(last, D(1))),
                Equal(C("coordinate", C("pathVertex", d, e, i)),
                    C("getElem", C("verifierExpand", corners), C("val", i))))),
            "endpoint_inventory" => Equal(C("image", pairFunction, C("univ", edge)), C("constructionEdges")),
            "endpoint_pair_injective" => C("Injective", pairFunction),
            "baseGraph_iff_endpoints" => All("a", original, All("b", original,
                Bicond(C("Adj", C("baseGraph"), a, b), Ex("e", edge,
                    Or(And(Equal(a, C("left", d, e)), Equal(b, C("right", d, e))),
                       And(Equal(a, C("right", d, e)), Equal(b, C("left", d, e)))))))),
            "routing_check_success" => Equal(routing, C("true")),
            "exact_square_routing" => And(C("Injective", C("coordinate")), exactAdj),
            "actual_T_bounds" => All("v", vertex,
                And(LessEqual(D(1), C("fst", rv)), And(LessEqual(C("fst", rv), D(9,3,3,7)),
                And(LessEqual(D(1), C("snd", rv)), LessEqual(C("snd", rv), D(9,0,6,1)))))),
            "inducedEmbedding" => Seq(C("inducedEmbedding"), Colon,
                C("GraphEmbedding", C("RoutedGraph"),
                    C("strongProduct", C("pathGraph", D(9,3,3,7)), C("pathGraph", D(9,0,6,1))))),
            "inducedIso" => Seq(C("inducedIso"), Colon,
                C("GraphIso", C("RoutedGraph"), C("induce", C("rectangle"), C("selected")))),
            "sum_subdivisions" => Equal(SumOver("e", edge, k), D(3,1,2,8,6)),
            "actual_vertex_count" => Equal(C("FintypeCard", vertex), D(9,3,9,9,9)),
            "actual_edge_count" => Equal(C("card", C("edgeFinset", C("RoutedGraph"))), D(9,4,0,3,6)),
            "selected_vertex_count" => Equal(C("FintypeCard", C("selected")), D(9,3,9,9,9)),
            "selected_edge_count" => Equal(C("card", C("edgeFinset", C("induce", C("rectangle"), C("selected")))), D(9,4,0,3,6)),
            _ => throw new System.ArgumentException(declaration),
        };
    }

    private static Formula LambdaTerm(string n, Formula t, Formula b) =>
        Seq(C("fun"), Sp, Open, I(n), Colon, t, Close, Sp, Mapsto, Sp, b);
    private static Formula SumOver(string n, Formula t, Formula b) =>
        Seq(new Formula.Subscript(Sum, Seq(I(n), Sp, InMacro, Sp, t)), Sp, b);
    private static Formula I(string n) => F.Id(n);
    private static Formula C(string n, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(n))
        : new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LessEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Bicond(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Statement(declaration))), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
