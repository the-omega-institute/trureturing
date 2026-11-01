using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Products;

internal sealed class LatticeRoutingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Products/LatticeRouting.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sparse occupancy checker certifies injectivity and both directions of lattice adjacency.",
        H("Induced lattice routing certificates"), Blocks(
            Paragraph(Text("Points are pairs of integers. Square adjacency means Manhattan distance one. The checker uses complete vertex and oriented-edge lists supplied by the actual graph construction. It neither assumes an embedding nor takes a certificate-correctness record as a hypothesis.")),
            Node("fresh-insert", "Occupancy.insert_spec", "Insertion records a fresh key and preserves old lookups",
                "A successful insertion gives read(next,key)=some(v) and preserves every previous successful lookup. Occupied keys are rejected even when their stored value equals the proposed value. Induction on the key proves this invariant.", DescribeRole.Theorem),
            Node("fill", "Occupancy.fill_spec", "Filling preserves occupancy and stores every listed vertex",
                "Successful fill preserves all old lookups and stores every a in xs at key(a). No injective hash assumption is needed: successful fresh insertion proves the needed uniqueness on the actual occupied vertices.", DescribeRole.Theorem),
            Node("soundness", "routingCheck_sound", "Success proves an induced routing",
                "Let f inject the vertices of H into the checked tag type of G. Every f(w) must occur in vs; H adjacency must be exactly the listed tag-pair inventory and must agree with G adjacency on the image of f. If routingCheck is true, c composed with f is injective and preserves and reflects H adjacency. Edge checking proves the forward implication. Four spatial queries per occupied tag and the fill invariant prove the reverse implication. A retrieved hash-collision value is checked against its actual coordinate. The concrete consumer proves its tag injection and graph correspondence; neither is an assumed certificate-correctness record.", DescribeRole.Theorem),
            Node("rotation", "rotation_adjacency", "The integral rotation preserves the required adjacency",
                "rotate(x,y)=(x+y+25,x-y+1705). The identity max(abs(a+b),abs(a-b))=abs(a)+abs(b) gives the exact equivalence, including all coordinate signs. The rotation is injective.", DescribeRole.Theorem),
            Node("strong", "strongProduct", "The actual strong product",
                "Adjacency is Mathlib boxProd adjacency or simultaneous adjacency in both factors. Thus one coordinate may stay fixed while the other follows an edge, or both may follow edges. This is the strong product required for king grids.", DescribeRole.Definition),
            Node("finite-paths", "strong_paths_iff", "Finite path factors give king adjacency",
                "For p,q in Fin n times Fin m, the strong product of the pinned Mathlib path graphs is adjacent exactly when the maximum absolute coordinate difference is one.", DescribeRole.Theorem),
            Node("rectangle", "oneBasedRectangleEmbedding", "Convert inclusive bounds into a finite induced embedding",
                "Given coordinate injectivity, exact square adjacency and bounds 1 <= rotate(c(v)).x <= n and 1 <= rotate(c(v)).y <= m for every v, subtract one from both rotated coordinates and obtain a graph embedding into Fin n times Fin m. A graph embedding reflects as well as preserves adjacency. The bounds and local checker remain actual proof obligations in its concrete consumer.", DescribeRole.Definition))));

    private static Formula Statement(string declaration)
    {
        var v = I("V"); var g = I("G"); var c = I("c");
        var a = I("a"); var b = I("b"); var q = I("q"); var w = I("w");
        var t = I("t"); var r = I("r"); var key = I("key"); var xs = I("xs");
        var n = I("n"); var m = I("m"); var p = I("p");
        var point = C("Point"); var tree = C("Occupancy", v);
        var some = (Formula x) => C("some", x);
        var preserve = All("q", C("List", C("Bool")), All("w", v,
            Imp(Equal(C("read", t, q), some(w)), Equal(C("read", r, q), some(w)))));
        var hadj = All("a", v, All("b", v,
            Bicond(C("Adj", g, a, b), C("squareAdj", C("apply", c, a), C("apply", c, b)))));
        var injection = C("Injective", c);
        var product = C("strongProduct", C("pathGraph", n), C("pathGraph", m));
        var finitePoint = C("Prod", C("Fin", n), C("Fin", m));
        var bounds = All("a", v, And(LessEqual(D(1), C("fst", C("rotate", C("apply", c, a)))),
            And(LessEqual(C("fst", C("rotate", C("apply", c, a))), n),
            And(LessEqual(D(1), C("snd", C("rotate", C("apply", c, a)))),
                LessEqual(C("snd", C("rotate", C("apply", c, a))), m)))));
        var vs = I("vs"); var es = I("es");
        var wt = I("W"); var h = I("H"); var f = I("f");
        var fa = C("apply", f, a); var fb = C("apply", f, b);
        var codedAdj = All("a", wt, All("b", wt,
            Bicond(C("Adj", g, fa, fb), C("Adj", h, a, b))));
        var codedInventory = All("a", wt, All("b", wt,
            Bicond(C("Adj", h, a, b), Or(C("ListMem", C("Pair", fa, fb), es),
                C("ListMem", C("Pair", fb, fa), es)))));
        var codedResult = And(C("Injective", C("comp", c, f)),
            All("a", wt, All("b", wt, Bicond(C("Adj", h, a, b),
                C("squareAdj", C("apply", c, fa), C("apply", c, fb))))));
        var codedPremises = Imp(C("Injective", f),
            Imp(All("a", wt, C("ListMem", fa, vs)), Imp(codedInventory,
            Imp(codedAdj, Imp(Equal(C("routingCheck", g, vs, es, c), C("true")), codedResult)))));
        var soundness = Checker(All("vs", C("List", v), All("es", C("List", C("Prod", v, v)),
            All("c", C("Function", v, point), All("W", C("Type"),
            All("H", C("SimpleGraph", wt), All("f", C("Function", wt, v), codedPremises)))))));
        return declaration switch
        {
            "Occupancy.insert_spec" => All("V", C("Type"), All("key", C("List", C("Bool")),
                    All("t", tree, All("r", tree, All("a", v,
                    Imp(Equal(C("insert", t, key, a), some(r)),
                        And(Equal(C("read", r, key), some(a)), preserve))))))),
            "Occupancy.fill_spec" => All("V", C("Type"), All("key", C("Function", v, C("List", C("Bool"))),
                    All("xs", C("List", v), All("t", tree, All("r", tree,
                    Imp(Equal(C("fill", key, xs, t), some(r)), And(preserve,
                        All("a", v, Imp(C("ListMem", a, xs),
                            Equal(C("read", r, C("apply", key, a)), some(a))))))))))),
            "routingCheck_sound" => soundness,
            "rotation_adjacency" => All("p", point, All("q", point,
                    Bicond(C("kingAdj", C("rotate", p), C("rotate", q)), C("squareAdj", p, q)))),
            "strongProduct" => All("V", C("Type"), All("W", C("Type"),
                    All("G", C("SimpleGraph", v), All("H", C("SimpleGraph", I("W")),
                    Seq(C("strongProduct", g, I("H")), Colon,
                        C("SimpleGraph", C("Prod", v, I("W")))))))),
            "strong_paths_iff" => All("n", C("Nat"), All("m", C("Nat"),
                    All("p", finitePoint, All("q", finitePoint,
                    Bicond(C("Adj", product, p, q), C("kingAdj", IntCoordinates(p), IntCoordinates(q))))))),
            "oneBasedRectangleEmbedding" => All("V", C("Type"), All("G", C("SimpleGraph", v),
                    All("c", C("Function", v, point), Imp(injection, Imp(hadj,
                    All("n", C("Nat"), All("m", C("Nat"),
                        Imp(bounds, C("GraphEmbedding", g, product))))))))),
            _ => throw new System.ArgumentException(declaration),
        };
    }

    private static Formula IntCoordinates(Formula p) => C("Pair",
        C("IntCast", C("val", C("fst", p))), C("IntCast", C("val", C("snd", p))));
    private static Formula Checker(Formula b) => All("V", C("Type"), Inst("DecidableEq", I("V"),
        All("G", C("SimpleGraph", I("V")), Inst("DecidableRel", C("Adj", I("G")), b))));
    private static Formula I(string n) => F.Id(n);
    private static Formula C(string n, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(n))
        : new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula All(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Inst(string n, Formula a, Formula b) => Seq(OpenBracket, C(n, a), CloseBracket, Sp, b);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LessEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Bicond(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);

    private static DocumentBlock Node(string id, string declaration, string title, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(declaration switch
            {
                "Occupancy.insert_spec" => "D5/S3/Combinatorics/Graph/Products/LatticeRouting/Occupancy.insert_spec",
                "Occupancy.fill_spec" => "D5/S3/Combinatorics/Graph/Products/LatticeRouting/Occupancy.fill_spec",
                _ => Prefix + declaration
            }), H(title),
            StatementSource.FromAuthor(Disp(Statement(declaration))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
