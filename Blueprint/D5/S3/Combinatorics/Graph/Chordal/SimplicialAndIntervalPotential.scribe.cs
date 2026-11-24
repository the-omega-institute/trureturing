using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class SimplicialAndIntervalPotentialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Chordal/SimplicialAndIntervalPotential.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simplicial averaging gives a finite-size reconstruction bound. Interval and split graphs admit a two-defect bound for bi-invariant pseudometrics.",
        H("Simplicial averaging and reconstruction on interval and split graphs"),
        Blocks(
            Result("simplicial-banach-gain-potential", "exists_simplicial_banach_gain_potential",
                "Simplicial averaging", BanachStatement(),
                "Here Natcard is the natural-number cardinality of the vertex type, including zero, and the subtraction in the exponent is natural-number subtraction. The function real denotes the natural-to-real cast, toSet denotes the underlying set of a finite set, and norm denotes the seminorm. Delete a simplicial vertex, apply induction to the remaining graph, and extend the potential by the mean of the candidates from its neighbors. A neighborhood has at most k vertices. The difference of any two candidates is bounded by the previous edge radius plus the triangle tolerance. The candidate at the tested edge contributes zero to the sum of differences. Thus the new radius is at most the fraction (k minus one) over k times the old radius plus the triangle tolerance inside the parentheses. Starting with radius zero on a single vertex solves the recurrence to give the displayed finite coefficient. The radius is nondecreasing with vertex count; if a vertex has no neighbors, its assigned value imposes no edge constraint. The coefficient is at most k minus one."),
            Result("interval-graph-two-defect", "intervalGraph_isChordal_and_two_approximate_gain_potential",
                "Finite interval graphs", IntervalStatement(),
                "In every nonempty subset of vertices, the interval with least right endpoint has pairwise intersecting neighbors in that subset. Applied to the support of a cycle, this gives a chord. For gain reconstruction begin at an interval with least left endpoint and fit all edges from that root exactly. Retain a neighbor of largest right endpoint and remove the rest of the closed neighborhood. The retained vertex has its left endpoint at most every remaining right endpoint. Repeat with this vertex as root, renormalizing the recursive potential at it. For any edge from the old neighborhood to the remaining vertices, its interval overlap forces both endpoints to meet the retained vertex. One triangle compares the two root spokes and the other compares the crossing edge against the path through the retained vertex. If the root has no neighbors it can be removed without an edge constraint. The group metric is invariant under both left and right multiplication. Reversal of an edge inverts its gain, so the ordered triangle condition is equivalent to bounding the distance of the triangle product from the identity."),
            Result("split-graph-two-defect", "exists_two_approximate_gain_potential_of_split",
                "Split graphs", SplitStatement(),
                "In each nonempty vertex subset, a vertex outside the clique, if present, has all its neighbors in the clique. Otherwise the subset is a clique. This gives chordality by taking the subset of vertices of a cycle. Choose a root of the clique if it is nonempty and assign each other clique vertex the gain from the root. Each non-clique vertex of positive degree is assigned the potential of any clique neighbor multiplied by the connecting gain. On clique edges the error is at most one triangle defect, and on any other edge the triangle through the chosen attachment and the clique comparison together cost at most two defects. Isolated vertices may be assigned arbitrary values."),
            Result("path-power-interval-representation", "pathPower_isIntervalGraph",
                "Path powers are interval graphs", PathStatement(),
                "The path power on Fin(n) joins distinct indices x and y when each is at most k greater than the other. The closed intervals from i to i plus k intersect exactly under these two inequalities. Thus the path-power lower bounds for Banach reconstruction are attained in the class of finite interval graphs. In the frozen lower bound the length factor tends to one at each fixed width, while the limiting width coefficient tends to two."))));

    private static DocumentBlock Result(string id, string name, string title, Formula formula, string proof) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(Par(premise), FormulaLogicOperator.Implies, Par(conclusion));
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Iff(Formula a, Formula b) => Seq(Par(a), Sp, Leftrightarrow, Sp, Par(b));
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Instance(string name, params Formula[] args) => Seq(OpenBracket, Call(name, args), CloseBracket, Sp);
    private static Formula Reals => Seq(Mathbb, Grp(V("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(V("N")));
    private static Formula Adj(Formula graph, Formula x, Formula y) => Call("Adj", graph, x, y);
    private static Formula Universes(Formula body) => All("u", Call("Universe"), All("v", Call("Universe"), body));

    private static Formula BanachStatement()
    {
        var vertices = V("V"); var graph = V("G"); var target = V("E");
        var k = V("k"); var s = V("s"); var i = V("i"); var j = V("j"); var l = V("l"); var eps = V("epsilon");
        Formula Gain(Formula a, Formula b) => Call("g", a, b);
        Formula Pot(Formula a) => Call("phi", a);
        var clique = All("s", Call("Finset", vertices),
            Imp(Call("IsClique", graph, Call("toSet", s)), Le(Call("card", s), Add(k, D(1)))));
        var reversal = All("i", vertices, All("j", vertices, Eq(Gain(j, i), Seq(Minus, Gain(i, j)))));
        var triangle = All("i", vertices, All("j", vertices, All("l", vertices,
            Imp(Adj(graph, i, j), Imp(Adj(graph, j, l), Imp(Adj(graph, i, l),
                Le(Call("norm", Sub(Add(Gain(i, j), Gain(j, l)), Gain(i, l))), eps)))))));
        var width = Call("real", k);
        var oneLess = Sub(width, D(1));
        var exponent = Sub(Call("Natcard", vertices), D(1));
        var radius = Mul(Mul(Par(oneLess), Par(Sub(D(1), new Formula.Power(
            Par(new Formula.Fraction(oneLess, width)), Par(exponent))))), eps);
        Formula result = Some("phi", Arrow(vertices, target), All("i", vertices, All("j", vertices,
            Imp(Adj(graph, i, j), Le(Call("norm", Sub(Gain(i, j), Par(Sub(Pot(j), Pot(i))))), radius)))));
        result = All("g", Arrow(vertices, Arrow(vertices, target)), All("epsilon", Reals,
            Imp(Le(D(0), eps), Imp(reversal, Imp(triangle, result)))));
        result = All("E", Call("Type", V("v")), Seq(Instance("SeminormedAddCommGroup", target),
            Instance("NormedSpace", Reals, target), Comma, Sp, result));
        result = All("k", Naturals, Imp(Le(D(2), k), Imp(clique, result)));
        result = All("V", Call("Type", V("u")), Seq(Instance("Finite", vertices), Comma, Sp,
            All("G", Call("SimpleGraph", vertices), Imp(Call("IsChordal", graph), result))));
        return Universes(result);
    }

    private static Formula IntervalHypotheses(Formula vertices, Formula graph, Formula body)
    {
        var i = V("i"); var j = V("j");
        Formula L(Formula x) => Call("l", x);
        Formula R(Formula x) => Call("r", x);
        var valid = All("i", vertices, Le(L(i), R(i)));
        var intersection = All("i", vertices, All("j", vertices,
            Iff(Adj(graph, i, j), And(Ne(i, j), Le(Call("max", L(i), L(j)), Call("min", R(i), R(j)))))));
        return All("l", Arrow(vertices, Reals), All("r", Arrow(vertices, Reals), Imp(valid, Imp(intersection, body))));
    }

    private static Formula GroupGains(Formula vertices, Formula graph, Formula group)
    {
        var i = V("i"); var j = V("j"); var l = V("l"); var eps = V("epsilon");
        Formula Gain(Formula a, Formula b) => Call("g", a, b);
        Formula Pot(Formula a) => Call("phi", a);
        var reversal = All("i", vertices, All("j", vertices,
            Imp(Adj(graph, i, j), Eq(Gain(j, i), Call("inv", Gain(i, j))))));
        var triangle = All("i", vertices, All("j", vertices, All("l", vertices,
            Imp(Adj(graph, i, j), Imp(Adj(graph, j, l), Imp(Adj(graph, i, l),
                Le(Call("dist", Mul(Gain(i, j), Gain(j, l)), Gain(i, l)), eps)))))));
        var fit = Some("phi", Arrow(vertices, group), All("i", vertices, All("j", vertices,
            Imp(Adj(graph, i, j), Le(Call("dist", Gain(i, j), Mul(Call("inv", Pot(i)), Pot(j))), Mul(D(2), eps))))));
        return All("g", Arrow(vertices, Arrow(vertices, group)), All("epsilon", Reals,
            Imp(Le(D(0), eps), Imp(reversal, Imp(triangle, And(Call("IsChordal", graph), fit))))));
    }

    private static Formula GroupHeader(Formula body, bool finite)
    {
        var vertices = V("V"); var group = V("H"); var graph = V("G");
        Formula instances = Seq(Instance("Group", group), Instance("PseudoMetricSpace", group),
            Instance("IsIsometricSMul", group, group), Instance("IsIsometricSMul", Call("MulOpposite", group), group));
        if (finite) instances = Seq(Instance("Finite", vertices), instances);
        return Universes(All("V", Call("Type", V("u")), All("H", Call("Type", V("v")),
            Seq(instances, Comma, Sp, All("G", Call("SimpleGraph", vertices), body)))));
    }

    private static Formula IntervalStatement() => GroupHeader(
        IntervalHypotheses(V("V"), V("G"), GroupGains(V("V"), V("G"), V("H"))), true);

    private static Formula SplitStatement() => GroupHeader(All("C", Call("Set", V("V")),
        Imp(Call("IsClique", V("G"), V("C")), Imp(Call("IsIndepSet", V("G"), Call("compl", V("C"))),
            GroupGains(V("V"), V("G"), V("H"))))), true);

    private static Formula PathStatement()
    {
        var n = V("n"); var k = V("k"); var vertices = Call("Fin", n);
        var graph = Call("pathPower", n, k); var i = V("i"); var j = V("j");
        Formula L(Formula x) => Call("l", x);
        Formula R(Formula x) => Call("r", x);
        return All("n", Naturals, All("k", Naturals, Some("l", Arrow(vertices, Reals),
            Some("r", Arrow(vertices, Reals), And(
                All("i", vertices, And(Eq(L(i), Call("real", Call("val", i))),
                    Eq(R(i), Add(Call("real", Call("val", i)), Call("real", k))))),
                And(All("i", vertices, Le(L(i), R(i))),
                    All("i", vertices, All("j", vertices, Iff(Adj(graph, i, j), And(Ne(i, j),
                        Le(Call("max", L(i), L(j)), Call("min", R(i), R(j)))))))))))));
    }
}
