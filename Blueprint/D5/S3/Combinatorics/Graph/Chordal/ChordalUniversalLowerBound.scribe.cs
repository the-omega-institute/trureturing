using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class ChordalUniversalLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Path powers admit uniform reconstruction with coefficient two. The width-three path on twelve vertices gives a sharp integral obstruction.",
        H("Sharp gain reconstruction on path powers"),
        Blocks(
            Paragraph(Text("The graph P(n,k) has vertex set Fin(n). Two distinct indices are adjacent when their difference has absolute value at most k.")),
            Result("path-power-chordal", "pathPower_isChordal", "Chordality of path powers",
                All("n", Naturals, All("k", Naturals, Call("Chordal", Graph(Id("n"), Id("k"))))),
                "Eliminate vertices in increasing order. The remaining neighbours of a vertex lie in the next k positions and hence form a clique."),
            Paragraph(Text("For multiplicative gains, R(G,g) means that the reversed gain is the inverse on each edge. T(G,g,e) means that on each ordered triangle the distance between the product along the first two sides and the gain along the third side is at most e. F(G,g,p,r) means that each directed edge gain is within distance r of the inverse of the potential at its tail times the potential at its head. The versions Radd, Tadd, and Fadd use negation, addition, and the head potential minus the tail potential. The functions edgeError(g,p,i,j) and edgeErrorAdd(g,p,i,j) are the respective multiplicative and additive distances at the single directed edge from i to j.")),
            Result("path-power-two-upper", "pathPower_exists_two_approximate_gain_potential", "Uniform coefficient two",
                All("H", Type, MetricGroup(Id("H"), All("n", Naturals, All("k", Naturals,
                    Imp(Le(D(1), Id("k")), Uniform(Graph(Id("n"), Id("k")), Vertices(Id("n")),
                        Id("H"), D(2))))))),
                "Join all vertices to their block heads and join successive heads. The tree potential compares each same-block edge with one triangle through its head. On a cross-block edge the earlier endpoint is adjacent to the later head, giving two triangle comparisons."),
            Paragraph(Text("Write X for the real cycle coordinates and L for their integral multiplicative counterpart. Both use the 19 coordinates outside the lexicographic greedy spanning tree. The filling norm is the infimum of the sum of absolute face coefficients over the 28 oriented triangles with the given boundary. The integer infimum is a minimum. The real filling norm makes X a finite-dimensional Banach space. Write gR for the canonical real gains, and gZ(n) for the integral gains pulled back along the map that sends vertices beyond 11 to 11.")),
            Result("path-power-both-lower-bounds", "pathPower_three_banach_and_integral_lower_bound",
                "Real and integral lower bounds on twelve vertices", BothBounds(),
                "The dual equality weights annihilate potential differences, because the boundary of each triangle has zero incidence at the vertices. The weighted residual functional is 98, and the column bounds give coefficients of total mass 96. The real maximum is therefore at least 49/48. Each integral filling is also a real filling, and its integral length raises the lower bound to two."),
            Result("path-power-exact-two", "pathPower_three_exact_two", "Exact coefficient in width three",
                All("n", Naturals, Imp(Le(D(12), Id("n")), IntegralBounds(Id("n"), true))),
                "Cloning the final vertex preserves the triangle condition. Each new triangle maps to an old triangle, a backtrack, or the diagonal. Restriction to the first twelve vertices preserves the obstruction. The block-head potential supplies the matching upper bound."),
            Result("chordal-sub-two-obstruction", "not_subtwo_universal_chordal",
                "Obstruction to a sub-two chordal coefficient",
                Seq(Neg, Par(Some("C", Reals, And(LtOf(Id("C"), D(2)),
                    All("V", Type, Seq(Instance("Finite", Id("V")),
                        All("G", Call("SimpleGraph", Id("V")),
                            Imp(Call("Chordal", Id("G")),
                                All("H", Type, MetricGroup(Id("H"),
                                    Uniform(Id("G"), Id("V"), Id("H"), Id("C"))))))))))),
                "Use the width-three graph on twelve vertices and its integral gains at triangle defect one. Every potential has an edge with error at least two."))));

    private static DocumentBlock Result(string id, string name, string title, Formula statement, string proof) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Par(Formula formula) => Seq(Open, formula, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula LtOf(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Type => Seq(Mathrm, Grp(Id("Type")));
    private static Formula Naturals => Seq(Mathbb, Grp(Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(Id("R")));
    private static Formula Vertices(Formula n) => Call("Fin", n);
    private static Formula Graph(Formula n, Formula k) => Call("P", n, k);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Instance(string name, params Formula[] args) =>
        Seq(OpenBracket, Call(name, args), CloseBracket, Sp);

    private static Formula MetricGroup(Formula h, Formula body) =>
        Seq(Instance("Group", h), Instance("PseudoMetricSpace", h), Instance("IsIsometricSMul", h, h),
            Instance("IsIsometricSMul", Seq(h, Caret, Grp(Id("op"))), h), body);

    private static Formula Uniform(Formula graph, Formula vertices, Formula target, Formula coefficient)
    {
        var g = Id("g");
        var e = Id("e");
        return All("g", Arr(vertices, Arr(vertices, target)), All("e", Reals,
            Imp(Le(D(0), e), Imp(Call("R", graph, g), Imp(Call("T", graph, g, e),
                Some("p", Arr(vertices, target), Call("F", graph, g, Id("p"), Mul(coefficient, e))))))));
    }

    private static Formula Lower(Formula graph, Formula vertices, Formula target, Formula gain,
        Formula threshold, string dist)
    {
        var i = Id("i");
        var j = Id("j");
        return All("p", Arr(vertices, target), Some("i", vertices, Some("j", vertices,
            And(Call("Adj", graph, i, j), Le(threshold, Call(dist, gain, Id("p"), i, j))))));
    }

    private static Formula IntegralBounds(Formula n, bool equality)
    {
        var graph = Graph(n, D(3));
        var vertices = Vertices(n);
        var gain = Call("gZ", n);
        var lower = Lower(graph, vertices, Id("L"), gain, D(2), "edgeError");
        var result = equality ? And(lower,
            Some("p", Arr(vertices, Id("L")), Call("F", graph, gain, Id("p"), D(2)))) : lower;
        return And(Call("R", graph, gain), And(Call("T", graph, gain, D(1)), result));
    }

    private static Formula BothBounds()
    {
        var graph = Graph(D(12), D(3));
        var gain = Id("gR");
        var ratio = Seq(Frac, Grp(D(49)), Grp(D(48)));
        return And(Call("Radd", graph, gain), And(Call("Tadd", graph, gain, D(1)),
            And(Lower(graph, Vertices(D(12)), Id("X"), gain, ratio, "edgeErrorAdd"),
                IntegralBounds(D(12), false))));
    }
}

