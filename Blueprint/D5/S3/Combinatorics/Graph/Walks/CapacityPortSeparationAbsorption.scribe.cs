using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class CapacityPortSeparationAbsorptionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/CapacityPortSeparationAbsorption.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distances between connected zero-capacity leaves in the original multigraph give both signed and rational capacity absorption bounds.",
        H("Separation and capacity absorption"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-adjacency"),
                DeclarationHandle.Create(Prefix + "originalGraph"),
                H("Original multigraph adjacency"), StatementSource.FromAuthor(Disp(GraphFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let V and E be arbitrary finite types, with incidence maps src,dst:E to V. Each e is an edge identity, including when several identities have the same endpoints. The original graph joins distinct vertices precisely when an edge identity has those endpoints in either order. Its extended distance is the length of a shortest walk and is infinite for disconnected pairs. Collapsing parallel adjacency does not change this distance: every adjacent step uses one original edge. Parallel edges remain distinct in the incidence degree and in C, the cardinality of E."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("separation-absorption"),
                DeclarationHandle.Create(Prefix + "actual_capacity_port_separation_absorption"),
                H("Absorption from the distance between leaves"),
                StatementSource.FromAuthor(Disp(MainFormula())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The maps src and dst have no loops. Capacities r:V to Nat satisfy degree(v) at most one when r(v)=0, and degree(v) at most 2r(v) when r(v)>0. Here degree counts incidences (e,false) and (e,true). A leaf is a vertex of capacity zero and degree one. No edge joins two such leaves. The natural number K is at least the number ell of leaf vertices. Set R=sum_v r(v), q=C−R, D=R+K and M=C+K. The signed quantities q,D are interpreted in Int; the fractional inequality is in Rat. In the formula, sum(r) denotes the sum over all vertices, and integer or rational casts are determined by the inequality in which they occur.")),
                    Paragraph(Text("For every natural d at least two, assume that each pair of distinct connected leaves has original graph distance at least d. Then D is at least (d+1)q, and ((d+1)/(d+2))M is at most D. Separately, if no two distinct leaves are connected, q is nonpositive. The second conclusion does not require choosing d or assuming a distance bound. Reachable and edist in the formula refer to originalGraph(src,dst), so disconnected pairs impose no finite-distance condition.")),
                    Paragraph(Text("Each positive-capacity vertex has exactly 2r(v) real and slack ports. A perfect matching on this even fiber supplies its local pairs. Zero-capacity vertices have only a single real leaf port or no ports. Combining the fiber matchings gives a base-preserving involution fixing exactly the leaf ports. Thus no routing is an additional hypothesis.")),
                    Paragraph(Text("Along any path of the port graph, a local pairing step preserves the original vertex and a real-edge step changes it along one original edge. Induction on the port walk and the graph-distance triangle inequality bound the distance between its bases by the number of real edges, with no charge for local steps. A component with two leaf ports has a terminal path whose real-edge count is exactly its component length. Its endpoints have distinct bases, because a degree-one leaf has only one real port. They are therefore distinct connected original leaves at distance at most that component length.")),
                    Paragraph(Text("The terminal counts give ell=2a+c and q=a−b, where a,b,c count LL, HH and LH components. Separation forces every LL component to contain at least d actual edges. Counting distinct edge identities by their port components gives C at least da, and K is at least 2a. Hence D=C−q+K is at least (d+1)q. This estimate holds for either sign of q. Substituting q=M−D and dividing by the positive d+2 gives the rational bound. If distinct leaves are never connected, there are no LL components; q=−b is nonpositive.")),
                    Paragraph(Text("Empty vertex and edge carriers, isolated vertices, arbitrary positive capacities and parallel edges are included. The statement is about abstract capacity multigraphs. It does not assert that a rectangular residual graph satisfies any particular distance lower bound, nor that its signed deficit is always nonpositive."))),
                DescribeRole.Theorem)), []));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);
    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Type() => new Formula.NamedConstant(FormulaIdentifier.Create("Type"));
    private static Formula Not(Formula body) => Seq(Neg, Sp, Open, body, Close);
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Maps(Formula body) => All("V", Type(), All("E", Type(),
        All("src", Arrow(Id("E"), Id("V")), All("dst", Arrow(Id("E"), Id("V")), body))));

    private static Formula GraphFormula()
    {
        var v = Id("v"); var t = Id("t"); var e = Id("e");
        var src = Id("src"); var dst = Id("dst");
        var forward = And(Eq(Call("apply", src, e), v), Eq(Call("apply", dst, e), t));
        var backward = And(Eq(Call("apply", src, e), t), Eq(Call("apply", dst, e), v));
        return Maps(All("v", Id("V"), All("t", Id("V"),
            Iff(Call("Adj", Call("originalGraph", src, dst), v, t),
                And(Ne(v, t), Or(Ex("e", Id("E"), forward), Ex("e", Id("E"), backward)))))));
    }

    private static Formula MainFormula()
    {
        var V = Id("V"); var E = Id("E"); var src = Id("src"); var dst = Id("dst");
        var r = Id("r"); var K = Id("K"); var d = Id("d");
        var v = Id("v"); var t = Id("t"); var e = Id("e");
        var G = Call("originalGraph", src, dst);
        var R = Call("sum", r); var C = Call("card", E);
        var rv = Call("apply", r, v); var deg = Call("degree", src, dst, v);
        Formula Leaf(Formula x) => Call("Leaf", src, dst, r, x);
        Formula Pairs(Formula body) => All("v", V, All("t", V,
            Imp(And(Leaf(v), And(Leaf(t), Ne(v, t))), body)));
        var loopless = All("e", E, Ne(Call("apply", src, e), Call("apply", dst, e)));
        var zero = All("v", V, Imp(Eq(rv, D(0)), Le(deg, D(1))));
        var positive = All("v", V, Imp(Le(D(1), rv), Le(deg, Mul(D(2), rv))));
        var leafedge = All("e", E, Not(And(Leaf(Call("apply", src, e)), Leaf(Call("apply", dst, e)))));
        var budget = Le(Call("card", Call("leafVertices", src, dst, r)), K);
        var separated = Pairs(Imp(Call("Reachable", G, v, t), Le(d, Call("edist", G, v, t))));
        var signed = Le(Mul(Add(d, D(1)), Sub(C, R)), Add(R, K));
        var fractional = Le(Mul(new Formula.Fraction(Add(d, D(1)), Add(d, D(2))), Add(C, K)), Add(R, K));
        var bounds = All("d", Nat(), Imp(And(Le(D(2), d), separated), And(signed, fractional)));
        var disconnected = Imp(Pairs(Not(Call("Reachable", G, v, t))), Le(Sub(C, R), D(0)));
        var conclusion = Imp(And(loopless, And(zero, And(positive, And(leafedge, budget)))),
            And(bounds, disconnected));
        return All("V", Type(), All("E", Type(), Instance(Call("Fintype", V),
            Instance(Call("Fintype", E), Instance(Call("DecidableEq", V),
                All("src", Arrow(E, V), All("dst", Arrow(E, V),
                    All("r", Arrow(V, Nat()), All("K", Nat(), conclusion)))))))));
    }
}
