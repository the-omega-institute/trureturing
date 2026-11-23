using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class ChordalBanachLimitTwoDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Chordal/ChordalBanachLimitTwo.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real Banach reconstruction coefficient of a path power tends to two minus two over its width.",
        H("The Banach reconstruction limit for path powers"),
        Blocks(
            Paragraph(Text("Write P(n,k) for the graph on Fin(n) joining distinct indices at distance at most k. Write R(V,g) for skew symmetry on every ordered pair in V. Write T(G,g,e) for triangle defect at most e in the target norm on every ordered triangle of G. For a potential p the edge residual is the gain from i to j minus the potential difference p(j) minus p(i). Its norm is denoted by error(g,p,i,j). The assertion F(G,g,p,e) bounds this norm by e on every ordered edge.")),
            Result("averaged-block-upper-bound", "pathPower_banach_upper_bound",
                "The averaged block upper bound",
                Width(All("n", Naturals, All("E", Type,
                    WithInstances(V("E"), false, Uniform(Graph(V("n"), V("k")), Vertices(V("n")),
                        V("E"), Coefficient(V("k"))))))),
                "For each offset integrate the gains along the clamped block heads and along the spokes. A cross-block edge is compared through the later head. The two triangle comparisons vanish respectively when the earlier and later endpoints are heads. Same-block comparisons cost at most one triangle, with zero error when the earlier endpoint is the head. Each endpoint is marked as a head by one offset. The norm of the mean residual is bounded by the mean of the norms."),
            Result("periodic-trace-lower-bound", "pathPower_banach_lower_bound",
                "The finite path lower bound", LowerBound(),
                "Use centered indicators of residues modulo the width and put the periodic gains in consecutive-edge gauge. Take the finite max norm over the individual samples and the sums in consecutive-edge windows. A triangle defect is a centered indicator or a difference of two indicators, so it has absolute sum at most one on every partial period. Sum the diagonal residuals of all width-length edges and subtract the residual sums of the consecutive edges. The full windows cancel and at most twice the width minus two boundary windows remain."),
            Result("path-power-banach-limit", "pathPower_banach_limit_tendsto", "The exact limit",
                Width(Call("Tendsto", MapVariable("n", Naturals, Call("CBan", V("n"), V("k"))),
                    Call("atTop", Naturals), Call("nhds", Coefficient(V("k"))))),
                "The coefficient is the infimum of the nonnegative uniform reconstruction constants at unit triangle defect. The prefactor in the lower bound tends to one for fixed width, so the upper and lower bounds have the same limit."),
            Result("no-subtwo-banach-chordal-bound", "not_subtwo_banach_chordal",
                "A chordal obstruction to every coefficient below two", Refutation(),
                "For each proposed coefficient below two, first choose the width and then the number of vertices so that the finite lower bound exceeds it. Every path power is chordal because the two cycle neighbours of a least vertex of a cycle of length at least four give a chord."))));

    private static DocumentBlock Result(string id, string name, string title, Formula statement, string proof) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Type => Seq(Mathrm, Grp(V("Type")));
    private static Formula Naturals => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals => Seq(Mathbb, Grp(V("R")));
    private static Formula Vertices(Formula n) => Call("Fin", n);
    private static Formula Graph(Formula n, Formula k) => Call("P", n, k);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Instance(string name, params Formula[] args) =>
        Seq(OpenBracket, Call(name, args), CloseBracket, Sp);

    private static Formula MapVariable(string name, Formula type, Formula body) =>
        Seq(Open, V(name), Colon, type, Sp, Mapsto, Sp, body, Close);

    private static Formula Coefficient(Formula k) => Sub(D(2), Div(D(2), k));
    private static Formula Width(Formula body) => All("k", Naturals, Imp(Le(D(1), V("k")), body));

    private static Formula WithInstances(Formula target, bool complete, Formula body) =>
        Seq(Instance(complete ? "NormedAddCommGroup" : "SeminormedAddCommGroup", target),
            Instance("NormedSpace", Reals, target),
            complete ? Seq(Instance("CompleteSpace", target), body) : body);

    private static Formula Uniform(Formula graph, Formula vertices, Formula target, Formula c)
    {
        var gain = V("g");
        var defect = V("e");
        return All("g", Arrow(vertices, Arrow(vertices, target)), All("e", Reals,
            Imp(Le(D(0), defect), Imp(Call("R", vertices, gain), Imp(Call("T", graph, gain, defect),
                Some("p", Arrow(vertices, target),
                    Call("F", graph, gain, V("p"), Mul(Par(c), defect))))))));
    }

    private static Formula LowerBound()
    {
        var n = V("n");
        var k = V("k");
        var vertices = Vertices(n);
        var graph = Graph(n, k);
        var target = V("E");
        var gain = V("g");
        var threshold = Mul(Div(Sub(n, k), Sub(Add(n, k), D(2))), Par(Coefficient(k)));
        var existsEdge = All("p", Arrow(vertices, target), Some("i", vertices, Some("j", vertices,
            And(Call("Adj", graph, V("i"), V("j")),
                Le(threshold, Call("error", gain, V("p"), V("i"), V("j")))))));
        var formula = Some("g", Arrow(vertices, Arrow(vertices, target)),
            And(Call("R", vertices, gain), And(Call("T", graph, gain, D(1)), existsEdge)));
        return Width(All("n", Naturals, Imp(Le(Add(k, D(1)), n), Some("E", Type,
            WithInstances(target, true, Seq(Instance("FiniteDimensional", Reals, target), formula))))));
    }

    private static Formula Refutation()
    {
        var v = V("V");
        var g = V("G");
        var target = V("E");
        var c = V("C");
        var targets = All("E", Type, WithInstances(target, true, Uniform(g, v, target, c)));
        var graphs = All("V", Type, Seq(Instance("Finite", v),
            All("G", Call("SimpleGraph", v), Imp(Call("Chordal", g), targets))));
        return Seq(Neg, Sp, Par(Some("C", Reals, And(Seq(c, Sp, F.Lt, Sp, D(2)), graphs))));
    }
}
