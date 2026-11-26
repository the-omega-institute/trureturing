using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class WeightedSimplicialBanachPotentialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Chordal/WeightedSimplicialBanachPotential.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted predecessor means and translated weighted clique means bound gain residuals.",
        H("Weighted gain reconstruction on chordal graphs and clique trees"),
        Blocks(
            Describe.Lean(DescribeId.Create("weighted-simplicial-gain-potential"),
                DeclarationHandle.Create(Prefix + "exists_weighted_simplicial_banach_gain_potential"),
                H("Weighted simplicial reconstruction"), StatementSource.FromAuthor(Disp(Simplicial())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Reverse a simplicial deletion order. Every predecessor neighborhood is a clique of size at most k, since adjoining the inserted vertex gives another clique. The potential is zero at a vertex with no predecessors. Use the uniform mean of the earlier candidates for a smaller neighborhood. For a neighborhood of size k, give its newest predecessor weight t and the others weight s, with s equal to one divided by one plus the displayed radius and t equal to one minus the other weights.")),
                    Paragraph(Text("The weighted residuals at an inserted vertex sum to zero. For an edge from the newest predecessor in a full neighborhood, the other predecessors lie in that vertex's own predecessor clique. When they exhaust that clique the earlier residuals cancel. When one vertex is omitted, subtract the old weighted zero sum to leave signed residual coefficients of total absolute mass at most twice s minus t.")),
                    Paragraph(Text("The new triangle defects cost at most k minus one times s. The quadratic inequality for the displayed radical ensures that the residual cost and defect cost together stay within the radius. The real operator casts natural numbers to the reals, and norm is the seminorm. The coefficients at k equal to two, three, four and five are respectively one, the golden ratio, three plus the square root of thirty-three divided by four with the division applied to the entire sum, and three."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("clique-tree-occurrence-center"),
                DeclarationHandle.Create(Prefix + "cliqueTree_occurrenceCenter_banach_potential"),
                H("Weighted clique-tree occurrence centers"), StatementSource.FromAuthor(Disp(Occurrence())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The tree T has clique bags K that cover the vertices and edges of G. The bags containing a fixed vertex contain all the bags on the tree paths between them. The distributions are indexed by the entire finite vertex type and vanish outside their bags. The sums use finite sets as their index domains, and natDiv denotes natural-number division.")),
                    Paragraph(Text("Each bag potential is the weighted mean of vertex stars. Its error on an edge omits both endpoint weights. Translate the bag potentials by constants so the mean difference on every separator vanishes. Subtract the smaller of the two weights at each common star before bounding the difference of the two residuals. Averaging the resulting increments over a separator omits the zero diagonal term.")),
                    Paragraph(Text("Choose a center in each vertex's occurrence subtree and use its translated value. Each endpoint of an edge moves by at most the product of its radius and the separator shift bound. At diameter one there are at most two occurrences of a vertex, so the midpoint of their translated values gives the second bound. At diameter zero every vertex has a unique occurrence."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Inst(string name, params Formula[] args) =>
        Seq(OpenBracket, Call(name, args), CloseBracket, Comma, Sp);
    private static Formula Adj(Formula graph, Formula x, Formula y) => Call("Adj", graph, x, y);
    private static Formula In(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula FiniteSum(Formula x, Formula domain, Formula item) =>
        Seq(new Formula.Subscript(Sum, In(x, domain)), Sp, item);

    private static Formula Gains(Formula coefficient, Formula? diameter = null, Formula? midpoint = null)
    {
        var vertices = V("V"); var graph = V("G"); var target = V("E");
        var u = V("i"); var v = V("j"); var w = V("l"); var eps = V("epsilon");
        Formula Gain(Formula a, Formula b) => Call("g", a, b);
        var skew = All("i", vertices, All("j", vertices, Eq(Gain(v, u), Seq(Minus, Gain(u, v)))));
        var triangle = All("i", vertices, All("j", vertices, All("l", vertices,
            Imp(Adj(graph, u, v), Imp(Adj(graph, v, w), Imp(Adj(graph, u, w),
                Le(Call("norm", Sub(Add(Gain(u, v), Gain(v, w)), Gain(u, w))), eps)))))));
        var residual = Call("norm", Sub(Gain(u, v), Par(Sub(Call("phi", v), Call("phi", u)))));
        Formula bounds = Le(residual, Mul(Par(coefficient), eps));
        if (diameter is not null && midpoint is not null)
            bounds = And(bounds, Imp(Le(diameter, D(1)), Le(residual, Mul(Par(midpoint), eps))));
        var fit = Some("phi", Arrow(vertices, target),
            All("i", vertices, All("j", vertices, Imp(Adj(graph, u, v), bounds))));
        return All("E", Call("Type", V("v")), Seq(Inst("SeminormedAddCommGroup", target),
            Inst("NormedSpace", R, target), All("g", Arrow(vertices, Arrow(vertices, target)),
                All("epsilon", R, Imp(Le(D(0), eps), Imp(skew, Imp(triangle, fit)))))));
    }

    private static Formula Simplicial()
    {
        var vertices = V("V"); var graph = V("G"); var k = V("k"); var clique = V("C");
        var cliqueBound = All("C", Call("Set", vertices),
            Imp(Call("IsClique", graph, clique), Le(Call("ncard", clique), Add(k, D(1)))));
        var width = Call("real", k);
        var radical = Call("sqrt", Sub(new Formula.Power(Par(Add(width, D(3))), D(2)), D(1, 6)));
        var radius = Call("max", Sub(width, D(2)), Div(Add(Sub(width, D(1)), radical), D(4)));
        var body = All("V", Call("Type", V("u")), Seq(Inst("Finite", vertices),
            All("G", Call("SimpleGraph", vertices), Imp(Call("IsChordal", graph),
                All("k", N, Imp(Le(D(2), k), Imp(cliqueBound, Gains(radius))))))));
        return All("u", Call("Universe"), All("v", Call("Universe"), body));
    }

    private static Formula Occurrence()
    {
        var vertices = V("V"); var indices = V("I"); var tree = V("T"); var graph = V("G");
        var a = V("a"); var b = V("b"); var x = V("x"); var y = V("y");
        var diameter = V("D"); var alpha = V("alpha"); var d = V("d");
        Formula Bag(Formula j) => Call("K", j);
        Formula Prob(Formula j, Formula z) => Call("pi", j, z);
        var separator = Call("intersection", Bag(a), Bag(b));
        var separators = All("a", indices, All("b", indices,
            Imp(Adj(tree, a, b), Call("Nonempty", separator))));
        var nonneg = All("a", indices, All("x", vertices, Le(D(0), Prob(a, x))));
        var support = All("a", indices, All("x", vertices,
            Imp(Seq(Neg, Sp, Par(In(x, Bag(a)))), Eq(Prob(a, x), D(0)))));
        var total = All("a", indices, Eq(FiniteSum(x, vertices, Prob(a, x)), D(1)));
        var local = All("a", indices, All("x", vertices, All("y", vertices,
            Imp(In(x, Bag(a)), Imp(In(y, Bag(a)), Imp(Adj(graph, x, y),
                Le(Sub(Sub(D(1), Prob(a, x)), Prob(a, y)), alpha)))))));
        var shared = FiniteSum(x, separator, Call("min", Prob(a, x), Prob(b, x)));
        var shift = Mul(Par(Sub(D(1), Div(D(1), Call("real", Call("ncard", separator))))),
            Par(Sub(D(1), shared)));
        var boundary = All("a", indices, All("b", indices, Imp(Adj(tree, a, b), Le(shift, d))));
        var diam = All("x", vertices, All("a", indices, All("b", indices,
            Imp(In(x, Bag(a)), Imp(In(x, Bag(b)), Le(Call("dist", tree, a, b), diameter))))));
        var radius = Call("real", Call("natDiv", Add(diameter, D(1)), D(2)));
        Formula body = All("D", N, Imp(diam, Gains(Add(alpha, Mul(Mul(D(4), radius), d)),
            diameter, Add(alpha, Mul(D(2), d)))));
        body = All("alpha", R, All("d", R,
            Imp(Le(D(0), alpha), Imp(Le(D(0), d), Imp(local, Imp(boundary, body))))));
        body = All("pi", Arrow(indices, Arrow(vertices, R)), Imp(nonneg, Imp(support, Imp(total, body))));
        body = All("K", Arrow(indices, Call("Set", vertices)),
            Imp(Call("IsCliqueTree", tree, graph, V("K")), Imp(separators, body)));
        body = All("V", Call("Type", V("u")), Seq(Inst("Fintype", vertices),
            All("I", Call("Type", V("w")), Seq(Inst("Finite", indices),
                All("T", Call("SimpleGraph", indices), All("G", Call("SimpleGraph", vertices), body))))));
        return All("u", Call("Universe"), All("v", Call("Universe"), All("w", Call("Universe"), body)));
    }
}
