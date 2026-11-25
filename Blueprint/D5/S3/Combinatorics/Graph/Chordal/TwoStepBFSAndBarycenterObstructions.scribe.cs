using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class TwoStepBFSAndBarycenterObstructionsDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Combinatorics/Graph/Chordal/TwoStepBFSAndBarycenterObstructions";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two finite chordal graph families force large errors for breadth-first reconstruction.",
        H("Obstructions to breadth-first gain reconstruction"),
        Blocks(
            Describe.Lean(DescribeId.Create("pure-predecessor-barycenter-unbounded"),
                DeclarationHandle.Create(Gid + ".pure_predecessor_barycenter_unbounded"),
                H("Pure predecessor averaging has unbounded error"),
                StatementSource.FromAuthor(Disp(TowerStatement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The tower has a root and n layers of m vertices. Each layer is a clique with one distinguished vertex at column zero. The first layer is adjacent to the root. From the next layer onward, column zero has only its distinguished predecessor, and each other vertex is adjacent to the entire preceding layer. Eliminating layers in reverse order, with column zero first in each layer, proves chordality. Edges change the layer by at most one and every vertex has a path down to the root.")),
                    Paragraph(Text("TowerGain is zero within layers and into the distinguished column, one on the remaining edges from the root or column zero, and two on the remaining edges. Reverse orientations have the opposite gain. Flat means skew with absolute triangle defect at most one. The two gains across any triangle spanning two consecutive layers differ by at most one.")),
                    Paragraph(Text("Pure means zero potential at the root and, at each vertex with predecessors, the arithmetic mean of predecessor potential plus incoming gain. Column zero has potential zero. Each other column starts at one and the next value is the sum of one and m minus one copies of the previous value plus two, divided by m. This recurrence has the displayed closed form. The within-layer edge from column zero realizes the value as its absolute residual. For fixed m these values approach twice m minus one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("two-step-bfs-root-averaging-lower-bound"),
                DeclarationHandle.Create(Gid + ".twoStepBFS_root_averaging_lower_bound"),
                H("Averaging over roots permits residuals approaching four"),
                StatementSource.FromAuthor(Disp(GadgetStatement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Gadget joins N copies along a path through their roots. In each copy the root meets A, the union of A and U is a clique, each v meets U and its matching vertex in A, and each y meets U and its matching v. Each indexed part has m vertices. The y vertices, then the v vertices, then U, then A, and finally the roots in path order give an elimination order.")),
                    Paragraph(Text("Anchors associates each component outside a root ball with a common predecessor of its shadow in the parent shadow, using the root at depth one. Weights gives each nonroot vertex a probability distribution supported on its BFS predecessors. The root potential is zero. At every other vertex the potential transports along successive anchors and adds the weighted mean of the gains on the two-edge paths from the anchor through the predecessors. Mean is the sum of these potentials weighted by the root law.")),
                    Paragraph(Text("A copy of root mass at most one over N exists by averaging. For any root outside that copy, distances in the copy increase by the distance to the copy root. The predecessors of each u are A, while the predecessors of each y are U and its matching v. The component of y in its tail consists of y alone, with shadow U and its matching v. The parent shadow is A. Its intersection with the earlier neighbors of the matching v forces the anchor for y to be the matching vertex in A, and the parent anchor is the copy root.")),
                    Paragraph(Text("Summing the two distinguished predecessor weights over all pairs of u and y gives at most twice m for each exterior root. Some pair has exterior mean total distinguished weight at most two over m. Ordering the vertices and assigning unit forward and negative unit backward gains gives defect one. The signed residual for each exterior root is four minus twice each distinguished weight. The general four-defect estimate bounds the absolute residual for each interior root. Combining the two root contributions yields the displayed coefficient."))),
                DescribeRole.Theorem))));

    private static Formula Id(string s) => F.Id(s);
    private static Formula App(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string n, Formula t, Formula f) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, f);
    private static Formula Ex(string n, Formula t, Formula f) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, f);
    private static Formula Par(Formula v) => Seq(Open, v, Close);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(Id("R")));
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Abs(Formula a) => Seq(Lvert, Sp, a, Rvert, Sp);
    private static Formula Fr(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Cast(Formula a) => App("real", a);

    private static Formula TowerStatement()
    {
        var m = Id("m"); var n = Id("n"); var i = Id("i"); var j = Id("j");
        var u = Id("u"); var v = Id("v"); var p = Id("phi"); var M = Id("M");
        var T = App("Tower", m, n); var V = App("TowerVertices", m, n);
        var gain = App("TowerGain", m, n); var vertex = App("LayerVertex", i, j);
        Formula pure = App("Pure", T, App("Root"), gain, p);
        Formula graphFacts = And(App("Chordal", T), And(App("Connected", T), App("Flat", T, gain)));
        Formula value = Sub(Sub(Seq(D(2), Cdot, Cast(m)), D(1)),
            Seq(Par(Sub(Seq(D(2), Cdot, Cast(m)), D(2))), Cdot,
                new Formula.Power(Par(Fr(Sub(Cast(m), D(1)), Cast(m))), i)));
        Formula pointwise = All("i", App("Fin", n), All("j", App("Fin", m),
            And(Eq(App("dist", T, App("Root"), vertex), Seq(i, Plus, D(1))),
                All("phi", Arrow(V, Real), Imp(pure,
                    Eq(App("eval", p, vertex), App("ifzero", j, D(0), value)))))));
        Formula exact = All("m", Nat, All("n", Nat, Imp(Le(D(2), m), Imp(Le(D(1), n),
            And(graphFacts, And(Ex("phi", Arrow(V, Real), pure), pointwise))))));
        Formula error = Abs(Sub(App("eval", gain, u, v),
            Par(Sub(App("eval", p, v), App("eval", p, u)))));
        Formula unbounded = All("M", Real, Ex("m", Nat, Ex("n", Nat,
            And(Le(D(2), m), And(Le(D(1), n), And(graphFacts, Ex("u", V, Ex("v", V,
                And(App("Adj", T, u, v), All("phi", Arrow(V, Real), Imp(pure, Lt(M, error))))))))))));
        return And(exact, unbounded);
    }

    private static Formula GadgetStatement()
    {
        var m = Id("m"); var n = Id("N"); var mu = Id("mu"); var a = Id("a");
        var w = Id("w"); var g = Id("g"); var r = Id("r"); var u = Id("u"); var v = Id("v");
        var G = App("Gadget", m, n); var V = App("GadgetVertices", m, n);
        var gainType = Arrow(V, Arrow(V, Real));
        Formula mean(Formula x) => App("Mean", G, mu, a, w, g, x);
        Formula error = Abs(Sub(App("eval", g, u, v), Par(Sub(mean(v), mean(u)))));
        Formula coefficient = Sub(Sub(D(4), Fr(D(4), Cast(m))), Fr(D(8), Cast(n)));
        Formula witness = Ex("g", gainType, And(App("Flat", G, g),
            Ex("u", V, Ex("v", V, And(App("Adj", G, u, v), Le(coefficient, error))))));
        Formula scheme = All("a", App("RootIndexedAnchors", G), All("w", Arrow(V, gainType),
            Imp(All("r", V, App("Anchors", G, r, App("eval", a, r))),
                Imp(All("r", V, App("Weights", G, r, App("eval", w, r))), witness))));
        Formula probability = All("mu", Arrow(V, Real),
            Imp(All("r", V, Le(D(0), App("eval", mu, r))), Imp(Eq(App("Sum", V, mu), D(1)), scheme)));
        return All("m", Nat, All("N", Nat, Imp(Le(D(2), m), Imp(Le(D(2), n),
            And(App("Chordal", G), And(App("Connected", G), probability))))));
    }
}
