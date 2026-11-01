using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Products;

internal sealed class PrescribedSubdivisionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Products/PrescribedSubdivision.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit fresh vertices, endpoint incidence and edge counts for prescribed triple subdivisions.",
        H("Prescribed graph subdivisions"), Blocks(
            Paragraph(Text("The original vertex type V and edge-index type E are arbitrary. Data D specifies distinct left and right endpoints and positive natural multiplicities k(e). No injectivity of the unordered endpoint pairs is assumed by this general construction. The concrete routing module supplies that property for its simple original graph.")),
            Node("vertices", "Vertex", "The actual fresh vertices",
                "Interior is the dependent sum of Fin (3 k(e)) over E. The sum tag distinguishes every old vertex from every fresh vertex, and the dependent edge tag distinguishes different routes. Interior index i denotes path position i+1.", DescribeRole.Definition),
            Node("path", "pathVertex", "Path positions and endpoints",
                "For an edge e, positions are 0 through 3 k(e)+1. Position zero is the old left endpoint, the last position is the old right endpoint, and intermediate positions use the corresponding fresh tag. Thus each edge is replaced by a path of 3 k(e)+1 edges.", DescribeRole.Definition),
            Node("path-injective", "pathVertex_injective", "Each prescribed path is simple",
                "For every e, distinct positions map to distinct actual vertices. Distinct endpoints, positivity and the explicit tags handle the endpoint and interior cases.", DescribeRole.Theorem),
            Node("incidence", "arc_iff_slot", "Every oriented edge has a literal slot",
                "For all vertices a,b, Arc a b holds exactly when a slot s produces the ordered pair (a,b). A slot consists of e and an index from 0 through 3 k(e). The graph symmetrizes Arc; there are no extra edges between old vertices or different fresh routes.", DescribeRole.Theorem),
            Node("edge-unique", "edge_injective", "No duplicate unordered path edge",
                "Different slots produce different unordered edges. Reversing an oriented edge cannot identify two slots because Arc is asymmetric. Parallel original endpoint pairs cause no collision among the fresh path edges.", DescribeRole.Theorem),
            Node("vertex-count", "card_vertices", "Exact vertex cardinality",
                "For finite V and E, the vertex cardinality is card(V) plus the sum over e of 3 k(e).", DescribeRole.Theorem),
            Node("edge-count", "card_edges", "Exact edge cardinality",
                "For finite V and E, the graph has exactly the sum over e of 3 k(e)+1 edges. The edge-inventory bijection supplies this count without enumerating vertex pairs. The module supplies no independence-complex or homology assertion.", DescribeRole.Theorem))));

    private static Formula Statement(string declaration)
    {
        var d = I("D"); var e = I("e"); var i = I("i");
        var vertex = C("Vertex", d); var slot = C("Slot", d);
        var fresh = Mul(D(3), C("k", d, e));
        var body = declaration switch
        {
            "Vertex" => Seq(vertex, Colon, C("Type")),
            "pathVertex" => All("e", I("E"), All("i", C("Fin", Add(fresh, D(2))),
                Seq(C("pathVertex", d, e, i), Colon, vertex))),
            "pathVertex_injective" => All("e", I("E"), C("Injective", C("pathVertex", d, e))),
            "arc_iff_slot" => All("a", vertex, All("b", vertex,
                Bicond(C("Arc", d, I("a"), I("b")),
                    Ex("s", slot, Equal(C("edgePair", d, I("s")), C("Pair", I("a"), I("b"))))))),
            "edge_injective" => C("Injective", C("edge", d)),
            "card_vertices" => Finite(Equal(C("FintypeCard", vertex),
                Add(C("FintypeCard", I("V")), SumOver("e", I("E"), fresh)))),
            "card_edges" => Finite(Equal(C("card", C("edgeFinset", C("graph", d))),
                SumOver("e", I("E"), Add(fresh, D(1)))), decidable: true),
            _ => throw new System.ArgumentException(declaration)
        };
        return All("V", C("Type"), All("E", C("Type"), All("D", C("Data", I("V"), I("E")), body)));
    }

    private static Formula Finite(Formula b, bool decidable = false)
    {
        if (decidable) b = Inst("DecidableEq", I("V"), Inst("DecidableEq", I("E"), b));
        return Inst("Fintype", I("V"), Inst("Fintype", I("E"), b));
    }
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
    private static Formula Inst(string n, Formula a, Formula b) => Seq(OpenBracket, C(n, a), CloseBracket, Sp, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Bicond(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);

    private static DocumentBlock Node(string id, string declaration, string title, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Statement(declaration))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
