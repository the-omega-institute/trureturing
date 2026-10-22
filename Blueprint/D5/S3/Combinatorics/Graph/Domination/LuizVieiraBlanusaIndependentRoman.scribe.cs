using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class LuizVieiraBlanusaIndependentRomanDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/Domination/LuizVieiraBlanusaIndependentRoman.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/luizvieira2025independentroman");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first generalized Blanuša snark has a [21]-Roman function of weight 108 and every independent [21]-Roman function has weight at least 110.",
        H("The Luiz–Vieira generalized Blanuša closing conjecture is false"),
        Blocks(
            Node("activeNbrs", "Active neighbours", ActiveNbrsFormula(),
                "Section 1: \"the active neighborhood of v under f, denoted by AN(v), is the set of vertices w ∈ N(v) such that f(w) ≥ 1.\" The filter is over the open neighbour finset.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsRomanDom", "[k]-Roman dominating functions", RomanFormula(),
                "Section 1: \"For any integer k ≥ 1, a [k]-Roman dominating function on G, also called [k]-RDF, is a function f : V(G) → {0, 1, . . . , k + 1} such that f(N[v]) ≥ k + |AN(v)| for every vertex v ∈ V(G) with f(v) < k.\" The displayed natural-valued encoding gives the same finite label interval.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsIndepRomanDom", "Independent [k]-Roman dominating functions", IndepRomanFormula(),
                "Section 1: \"A [k]-Roman dominating function f = (V0, V1, . . . , Vk+1) on a graph G is called an independent [k]-Roman dominating function, or [k]-IRDF for short, if the set of active vertices V1 ∪ V2 ∪ · · · ∪ Vk+1 is an independent set.\" Positive labels encode the active set.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("weight", "Roman weight", WeightFormula(),
                "Section 1: \"The weight of a [k]-RDF f on G is defined as ω(f) = f(V(G)) = Σ_{v∈V(G)} f(v).\"", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("gammaRoman", "[k]-Roman domination number", GammaFormula("gammaRoman", "IsRomanDom"),
                "Section 1: \"The [k]-Roman domination number of G is the minimum weight that a [k]-RDF of G can have, and is denoted by γ[kR](G).\"", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("indepRoman", "Independent [k]-Roman domination number", GammaFormula("indepRoman", "IsIndepRomanDom"),
                "Section 1: \"The independent [k]-Roman domination number i[kR](G) is the minimum weight of an independent [k]-IRDF on G\".", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Vert", "Blanuša vertex labels", VertFormula(),
                "The inductive type has exactly the two displayed constructors. Figure 5 labels the ten vertices of B₀ᵗ by blk 0 through blk 9 and the eight vertices of each link Lⱼ by lnk j 0 through lnk j 7.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a", "Block border vertex a", ConstFormula("a", "Vert.blk", D(0)), "Figure 5(a) names a = blk 0.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("b", "Block border vertex b", ConstFormula("b", "Vert.blk", D(6)), "Figure 5(a) names b = blk 6.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("c", "Block border vertex c", ConstFormula("c", "Vert.blk", D(3)), "Figure 5(a) names c = blk 3.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("d", "Block border vertex d", ConstFormula("d", "Vert.blk", D(9)), "Figure 5(a) names d = blk 9.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("x", "Link border vertex x", LinkBorderFormula("x", 0), "Figure 5(c) names xⱼ = lnk j 0.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("w", "Link border vertex w", LinkBorderFormula("w", 2), "Figure 5(c) names wⱼ = lnk j 2.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("y", "Link border vertex y", LinkBorderFormula("y", 5), "Figure 5(c) names yⱼ = lnk j 5.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("z", "Link border vertex z", LinkBorderFormula("z", 7), "Figure 5(c) names zⱼ = lnk j 7.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("blockOneEdges", "Edges of B₀¹", ConcreteFormula("blockOneEdges", "Sym2 Vert", BlockOne()), "Figure 5(a) gives the thirteen unordered edges of B₀¹.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("blockTwoEdges", "Edges of B₀²", ConcreteFormula("blockTwoEdges", "Sym2 Vert", BlockTwo()), "Figure 5(b) gives the thirteen unordered edges of B₀².", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("linkEdges", "Edges of Lⱼ", LinkEdgesFormula(), "Figure 5(c) gives the ten edges of each link block Lⱼ.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("blockEdges", "Base block edge selector", Disp(All("t", Nat, Eqf(Call("blockEdges", X("t")), If(Eqf(X("t"), D(1)), Call("blockOneEdges"), Call("blockTwoEdges"))))), "The base block is B₀¹ when t = 1 and B₀² otherwise.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("linkVerts", "Vertices of Lⱼ", Disp(All("j", Nat, Eqf(Call("linkVerts", X("j")), App(Q("Finset", "image"), Lambda("r", Fin(D(8)), App(Q("Vert", "lnk"), X("j"), X("r"))), Q("Finset", "univ"))))), "Each Lⱼ has the eight vertices lnk j r for r ∈ Fin 8.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("linkGraphEdges", "Edges of the link graph", LinkGraphFormula(), "Section 4, Figure 8: E(LGᵢ) = E(Lᵢ₋₁) ∪ E(Lᵢ) ∪ {wᵢ₋₁yᵢ, zᵢ₋₁xᵢ}.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("verts", "Vertices of Bᵢᵗ", VertsFormula(), "Section 4: V(Bᵢᵗ) is the base block together with the required link blocks, recursively adding two links at each step.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("edges", "Edges of Bᵢᵗ", EdgesFormula(), "Section 4: \"For each integer i, with i ≥ 3, the snark Bᵢᵗ is obtained recursively from the snark Bᵗᵢ₋₂ and the link graph LGᵢ\" with the displayed edge deletion and insertion sets.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("snark", "Generalized Blanuša snark", SnarkFormula(), "The graph Bᵢᵗ is the SimpleGraph.fromRel graph on the vertex subtype v ∈ verts i, with adjacency represented by Sym2.mk membership in edges t i.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The closing conjecture", Disp(IffFormula(X("claim"), ClaimBody())), "Section 6: \"another interesting line of research is finding other classes of graphs with ∆(G) ≤ 3 for which γ[kR](G) = i[kR](G) for k ≥ 2. In fact, we conjecture that this property holds for all generalized Blanuša snarks.\" The parameters are encoded by t ∈ {1, 2}, i ≥ 1 and k ≥ 2.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A counterexample at B₁¹ and k = 21", Disp(new Formula.Not(ClaimBody())), "For B₁¹, the constant label 6 is a [21]-RDF of weight 108, while the independent witness has five positive labels of 22 and hence weight 110. Thus γ[21R](B₁¹) ≤ 108 < 110 = i[21R](B₁¹), refuting the closing conjecture.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("luiz-vieira-2024-blanusa-independent-roman-closing-conjecture"),
                    ResolutionKind.Refuted))
        ), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("lv-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula Type => X("Type");
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Adj(Formula g) => App(Q("SimpleGraph", "Adj"), g);
    private static Formula Inst(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqf(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Mem(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffFormula(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Lambda(string name, Formula type, Formula body) => Parenthesized(Seq(Operatorname, Grp(X("fun")), Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula If(Formula condition, Formula yes, Formula no) => Call("ite", condition, yes, no);
    private static Formula Edge(Formula left, Formula right) => App(Q("Sym2", "mk"), left, right);
    private static Formula Blk(int n) => App(Q("Vert", "blk"), D((byte)n));
    private static Formula Lnk(Formula j, int n) => App(Q("Vert", "lnk"), j, D((byte)n));
    private static Formula Set(params Formula[] values) => new Formula.SetLiteral([.. values]);
    private static Formula Union(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Cup, Sp, Parenthesized(right));
    private static Formula Difference(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Setminus, Sp, Parenthesized(right));

    private static Formula ActiveNbrsFormula()
    {
        var v = X("V"); var g = X("G"); var f = X("f"); var x = X("v"); var u = X("u");
        var body = Eqf(Call("activeNbrs", g, f, x), App(Q("Finset", "filter"), Lambda("u", v, Lt(D(0), App(f, u))), App(Q("SimpleGraph", "neighborFinset"), g, x)));
        var functions = All("f", new Formula.TypeArrow(v, Nat), All("v", v, body));
        return Disp(All("V", Type, Inst(Call("Fintype", v), All("G", Call("SimpleGraph", v), Inst(Call("DecidableRel", Adj(g)), functions)))));
    }

    private static Formula RomanFormula()
    {
        var v = X("V"); var g = X("G"); var k = X("k"); var f = X("f"); var x = X("v");
        var bound = All("v", v, Le(App(f, x), Add(k, D(1))));
        var cond = Imp(Lt(App(f, x), k), Le(Add(k, App(Q("Finset", "card"), Call("activeNbrs", g, f, x))), Add(App(f, x), App(Q("Finset", "sum"), App(Q("SimpleGraph", "neighborFinset"), g, x), f))));
        var functions = All("k", Nat, All("f", new Formula.TypeArrow(v, Nat), IffFormula(Call("IsRomanDom", g, k, f), And(bound, All("v", v, cond)))));
        return Disp(All("V", Type, Inst(Call("Fintype", v), All("G", Call("SimpleGraph", v), Inst(Call("DecidableRel", Adj(g)), functions)))));
    }

    private static Formula IndepRomanFormula()
    {
        var v = X("V"); var g = X("G"); var k = X("k"); var f = X("f"); var u = X("u"); var w = X("w");
        var independent = All("u", v, All("w", v, Imp(Lt(D(0), App(f, u)), Imp(Lt(D(0), App(f, w)), new Formula.Not(App(Adj(g), u, w))))));
        var functions = All("k", Nat, All("f", new Formula.TypeArrow(v, Nat), IffFormula(Call("IsIndepRomanDom", g, k, f), And(Call("IsRomanDom", g, k, f), independent))));
        return Disp(All("V", Type, Inst(Call("Fintype", v), All("G", Call("SimpleGraph", v), Inst(Call("DecidableRel", Adj(g)), functions)))));
    }

    private static Formula WeightFormula() => Disp(All("V", Type, Inst(Call("Fintype", X("V")), All("f", new Formula.TypeArrow(X("V"), Nat), Eqf(Call("weight", X("f")), App(Q("Finset", "sum"), Q("Finset", "univ"), X("f")))))));

    private static Formula GammaFormula(string name, string predicate)
    {
        var v = X("V"); var g = X("G"); var k = X("k"); var w = X("w"); var f = X("f");
        var witness = Some("f", new Formula.TypeArrow(v, Nat), And(Call(predicate, g, k, f), Eqf(Call("weight", f), w)));
        var set = Seq(OpenBrace, w, Sp, Colon, Sp, Nat, Sp, Mid, Sp, witness, CloseBrace);
        var numbers = All("k", Nat, Eqf(Call(name, g, k), Call("sInf", set)));
        return Disp(All("V", Type, Inst(Call("Fintype", v), All("G", Call("SimpleGraph", v), Inst(Call("DecidableRel", Adj(g)), numbers)))));
    }

    private static Formula VertFormula() => Disp(new Formula.Aligned([
        Seq(Q("Vert", "blk"), Sp, Colon, Sp, new Formula.TypeArrow(Fin(D(1, 0)), Call("Vert"))),
        Seq(Q("Vert", "lnk"), Sp, Colon, Sp, new Formula.TypeArrow(Nat, new Formula.TypeArrow(Fin(D(8)), Call("Vert"))))
    ]));
    private static Formula ConstFormula(string name, string owner, Formula value)
    {
        var pieces = owner.Split('.');
        return Disp(Eqf(Call(name), App(Q(pieces[0], pieces[1]), value)));
    }
    private static Formula LinkBorderFormula(string name, int index) => Disp(All("j", Nat, Eqf(Call(name, X("j")), Lnk(X("j"), index))));
    private static Formula ConcreteFormula(string name, string type, Formula value) => Disp(Eqf(Call(name), value));

    private static Formula BlockOne() => Set(Edge(Blk(0), Blk(1)), Edge(Blk(1), Blk(2)), Edge(Blk(2), Blk(3)), Edge(Blk(3), Blk(9)), Edge(Blk(9), Blk(8)), Edge(Blk(8), Blk(7)), Edge(Blk(7), Blk(6)), Edge(Blk(6), Blk(4)), Edge(Blk(4), Blk(0)), Edge(Blk(1), Blk(7)), Edge(Blk(2), Blk(5)), Edge(Blk(5), Blk(8)), Edge(Blk(4), Blk(5)));
    private static Formula BlockTwo() => Set(Edge(Blk(0), Blk(1)), Edge(Blk(1), Blk(3)), Edge(Blk(1), Blk(2)), Edge(Blk(2), Blk(8)), Edge(Blk(2), Blk(5)), Edge(Blk(0), Blk(4)), Edge(Blk(4), Blk(6)), Edge(Blk(4), Blk(5)), Edge(Blk(5), Blk(7)), Edge(Blk(3), Blk(7)), Edge(Blk(7), Blk(9)), Edge(Blk(6), Blk(8)), Edge(Blk(8), Blk(9)));
    private static Formula LinkEdgesFormula()
    {
        var j = X("j");
        var e = Set(Edge(Lnk(j, 0), Lnk(j, 1)), Edge(Lnk(j, 1), Lnk(j, 2)), Edge(Lnk(j, 2), Lnk(j, 4)), Edge(Lnk(j, 4), Lnk(j, 7)), Edge(Lnk(j, 7), Lnk(j, 6)), Edge(Lnk(j, 6), Lnk(j, 5)), Edge(Lnk(j, 5), Lnk(j, 3)), Edge(Lnk(j, 3), Lnk(j, 0)), Edge(Lnk(j, 1), Lnk(j, 6)), Edge(Lnk(j, 3), Lnk(j, 4)));
        return Disp(All("j", Nat, Eqf(Call("linkEdges", j), e)));
    }
    private static Formula LinkGraphFormula()
    {
        var i = X("i");
        return Disp(All("i", Nat, Eqf(Call("linkGraphEdges", i), Union(Union(Call("linkEdges", Sub(i, D(1))), Call("linkEdges", i)), Set(Edge(Call("w", Sub(i, D(1))), Call("y", i)), Edge(Call("z", Sub(i, D(1))), Call("x", i)))))));
    }
    private static Formula VertsFormula()
    {
        var i = X("i");
        var zero = App(Q("Finset", "image"), Q("Vert", "blk"), Q("Finset", "univ"));
        return Disp(new Formula.Aligned([
            Eqf(Call("verts", D(0)), zero),
            Eqf(Call("verts", D(1)), Union(zero, Call("linkVerts", D(1)))),
            Eqf(Call("verts", D(2)), Union(Union(zero, Call("linkVerts", D(1))), Call("linkVerts", D(2)))),
            All("i", Nat, Eqf(Call("verts", Add(i,D(3))), Union(Call("verts", Add(i,D(1))), Union(Call("linkVerts", Add(i,D(2))), Call("linkVerts", Add(i,D(3)))))))
        ]));
    }
    private static Formula EdgesFormula()
    {
        var t = X("t"); var i = X("i");
        var one = Union(Call("blockEdges",t), Call("linkEdges",D(1)));
        var two = Union(one, Call("linkEdges",D(2)));
        var firstOne = Set(Edge(Call("c"),Call("y",D(1))), Edge(Call("d"),Call("x",D(1))), Edge(Call("a"),Call("z",D(1))), Edge(Call("b"),Call("w",D(1))));
        var firstTwo = Set(Edge(Call("b"),Call("w",D(1))), Edge(Call("a"),Call("z",D(1))), Edge(Call("c"),Call("y",D(1))), Edge(Call("d"),Call("x",D(1))));
        var secondOne = Set(Edge(Call("c"),Call("y",D(1))), Edge(Call("d"),Call("x",D(1))), Edge(Call("w",D(1)),Call("y",D(2))), Edge(Call("z",D(1)),Call("x",D(2))), Edge(Call("a"),Call("z",D(2))), Edge(Call("b"),Call("w",D(2))));
        var secondTwo = Set(Edge(Call("b"),Call("w",D(2))), Edge(Call("a"),Call("z",D(2))), Edge(Call("c"),Call("y",D(1))), Edge(Call("d"),Call("x",D(1))), Edge(Call("z",D(1)),Call("x",D(2))), Edge(Call("w",D(1)),Call("y",D(2))));
        var removed = Set(Edge(Call("a"),Call("z",Add(i,D(1)))), Edge(Call("b"),Call("w",Add(i,D(1)))));
        var incoming = Set(Edge(Call("w",Add(i,D(1))),Call("y",Add(i,D(2)))), Edge(Call("z",Add(i,D(1))),Call("x",Add(i,D(2)))), Edge(Call("a"),Call("z",Add(i,D(3)))), Edge(Call("b"),Call("w",Add(i,D(3)))));
        var recursive = Union(Union(Difference(Call("edges",t,Add(i,D(1))),removed), Call("linkGraphEdges",Add(i,D(3)))),incoming);
        return Disp(All("t",Nat,new Formula.Aligned([
            Eqf(Call("edges",t,D(0)),Call("blockEdges",t)),
            Eqf(Call("edges",t,D(1)),If(Eqf(t,D(1)),Union(one,firstOne),Union(one,firstTwo))),
            Eqf(Call("edges",t,D(2)),If(Eqf(t,D(1)),Union(two,secondOne),Union(two,secondTwo))),
            All("i",Nat,Eqf(Call("edges",t,Add(i,D(3))),recursive))
        ])));
    }
    private static Formula SnarkFormula()
    {
        var t = X("t"); var i = X("i"); var v = X("v"); var u = X("u");
        var vertexType = Call("Subtype", Lambda("q", Call("Vert"), Mem(X("q"), Call("verts", i))));
        var relation = Lambda("u", vertexType, Lambda("v", vertexType, Mem(Edge(App(Q("Subtype", "val"), u), App(Q("Subtype", "val"), v)), Call("edges", t, i))));
        return Disp(All("t", Nat, All("i", Nat, Eqf(Call("snark", t, i), App(Q("SimpleGraph", "fromRel"), relation)))));
    }
    private static Formula ClaimBody()
    {
        var t = X("t"); var i = X("i"); var k = X("k");
        return All("t", Nat, All("i", Nat, All("k", Nat, Imp(Or(Eqf(t, D(1)), Eqf(t, D(2))), Imp(Le(D(1), i), Imp(Le(D(2), k), Eqf(Call("gammaRoman", Call("snark", t, i), k), Call("indepRoman", Call("snark", t, i), k))))))));
    }
}
