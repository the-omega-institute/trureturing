using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class ThreeTreeBanachSharpBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Chordal/ThreeTreeBanachSharpBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A polygon invariant bounds Banach gain reconstruction on clique-four chordal graphs. Third powers of paths have supremum reconstruction coefficient four thirds.",
        H("Banach reconstruction on clique-four chordal graphs"),
        Blocks(
            Paragraph(Text("Let skew(V,g) mean that reversing a gain negates it for every ordered pair of vertices in V. Let flat(G,g,e) mean that the norm of g(i,j) plus g(j,k) minus g(i,k) is at most e on every ordered triangle of G. Write err(g,p,i,j) for the norm of g(i,j) minus the entire difference (p(j) minus p(i)). The predicate fit(G,g,p,e) requires this norm to be at most e on every ordered edge.")),
            Entry("clique-four-polygon", "exists_cliqueFour_banach_gain_potential_polygon",
                "Reconstruction from the invariant polygon", ChordalUpper(),
                "Use a reverse perfect elimination order. For an ordered parent triangle record the two consecutive residuals and its defect. The middle residual into the next vertex is a fixed linear expression in those two residuals and three defects. Each of the nine signed transitions preserves the thirteen polygon inequalities by nonnegative combinations of pairs of parent inequalities. Six signed possibilities cover every admissible scalar defect quadruple by convex combinations.",
                "A single predecessor fixes the new potential by exact transport. For two predecessors append a virtual copy of the later predecessor. Its potential puts the parent in the zero-defect layer, and midpoint interpolation gives opposite half-defects on the two virtual child faces. The child face of the three actual vertices therefore carries the invariant into later attachments. Apply the scalar argument to each norm-one-or-smaller functional and use a norming functional to recover the edge norm. An arbitrarily small positive allowance handles zero defect tolerance."),
            Entry("third-power-of-a-path", "pathPowerThree", "The path graph",
                All("n", Naturals, Eq(Path(V("n")), Call("pathPower", V("n"), D(3)))),
                "The graph joins distinct indices at distance at most three.", DescribeRole.Definition),
            Entry("path-causal-upper", "pathPowerThree_banach_upper_four_thirds",
                "A causal path potential", PathUpper(),
                "Integrate along the adjacent edges, then subtract that gradient. Call the remaining gains on lengths two and three a and b. Clamp the indices at the endpoints, and give the new potential the increment at i equal to one third of b at i minus two, minus a at i minus two, plus a at i minus one. The residuals on lengths one, two, and three sum two, three, and four terms respectively, each bounded by the triangle tolerance, and divide by three."),
            Entry("hexagonal-target", "pathHexagon", "The hexagonal plane",
                All("x", Arrow(Call("Fin", D(3)), Reals), new Formula.Logic(
                    new Formula.Relation(V("x"), FormulaRelationOperator.MemberOf, V("Hex")), FormulaLogicOperator.Iff,
                    Eq(Add(Add(Call("x", D(0)), Call("x", D(1))), Call("x", D(2))), D(0)))),
                "The norm is the restriction of the supremum norm on the three coordinates.", DescribeRole.Definition),
            Entry("path-hexagonal-lower", "pathPowerThree_banach_lower_four_thirds",
                "A finite planar lower bound", PathLower(),
                "The length-three gain is two thirds in every coordinate except the initial index modulo three, where it is minus four thirds. A length-two gain averages the current and previous length-three gains. Adjacent gains vanish. Sum the residuals along each of the three length-three residue classes, taking its corresponding coordinate. The zero coordinate sums at the two middle endpoints leave four adjacent-edge differences. If M bounds the residuals, the resulting inequality is four times m at most three times m plus four, multiplied by M."),
            Entry("path-power-supremum", "pathPowerThree_banach_sup_four_thirds",
                "Supremum over path lengths", Eq(Call("sup", Map("n", Naturals, Call("CBan", V("n"), D(3)))), FourThirds),
                "Here CBan is the infimum of nonnegative uniform reconstruction coefficients at unit defect for the indicated path power. The causal formula supplies a common upper bound. The planar lower bounds approach it as the residue classes lengthen."),
            Entry("clique-four-coefficient", "cliqueFourBanachCoefficient", "The clique-four coefficient",
                Eq(V("S"), Call("inf", Call("Good"))),
                "Good is the set of nonnegative real coefficients giving a uniform potential bound at unit triangle defect for every finite chordal graph of clique number at most four and every real Banach target. S is the infimum of Good.", DescribeRole.Definition),
            Entry("clique-four-interval", "cliqueFour_banach_coefficient_bounds",
                "The clique-four interval", And(Le(FourThirds, V("S")), And(Le(V("S"), PolygonRadius), Lt(PolygonRadius, Div(D(3), D(2))))),
                "Every admissible coefficient bounds the finite hexagonal examples because these path powers are chordal and have no clique of size five. The polygon coefficient is itself admissible."))));

    private static DocumentBlock Entry(string id, string name, string title, Formula statement, string proof,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(statement)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(proof))), role);

    private static DocumentBlock Entry(string id, string name, string title, Formula statement, string first, string second) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(first)), Paragraph(Text(second))), DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula Naturals => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals => Seq(Mathbb, Grp(V("R")));
    private static Formula PolygonRadius => Div(D(7, 2, 5, 3, 7), D(5, 0, 0, 0, 0));
    private static Formula FourThirds => Div(D(4), D(3));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(V(name))) : new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Map(string name, Formula type, Formula body) =>
        Seq(Open, V(name), Colon, type, Sp, Mapsto, Sp, body, Close);
    private static Formula Instance(string name, params Formula[] args) => Seq(OpenBracket, Call(name, args), CloseBracket, Sp);
    private static Formula Path(Formula n) => Call("P", n);

    private static Formula Uniform(Formula graph, Formula vertices, Formula radius)
    {
        var target = V("E"); var gain = V("g"); var epsilon = V("e");
        return All("v", Call("Universe"), All("E", Call("Type", V("v")),
            Seq(Instance("SeminormedAddCommGroup", target), Instance("NormedSpace", Reals, target),
                All("g", Arrow(vertices, Arrow(vertices, target)), All("e", Reals,
                    Imp(Le(D(0), epsilon), Imp(Call("skew", vertices, gain), Imp(Call("flat", graph, gain, epsilon),
                        Some("p", Arrow(vertices, target), Call("fit", graph, gain, V("p"), Mul(Par(radius), epsilon))))))))));
    }

    private static Formula ChordalUpper()
    {
        var vertices = V("V"); var graph = V("G"); var clique = V("A");
        var card = All("A", Call("Set", vertices),
            Imp(Call("IsClique", graph, clique), Le(Call("ncard", clique), D(4))));
        return All("u", Call("Universe"), All("V", Call("Type", V("u")), Seq(Instance("Fintype", vertices),
            All("G", Call("SimpleGraph", vertices), Imp(Call("IsChordal", graph), Imp(card,
                Uniform(graph, vertices, PolygonRadius)))))));
    }

    private static Formula PathUpper() => All("n", Naturals, Uniform(Path(V("n")), Call("Fin", V("n")), FourThirds));

    private static Formula PathLower()
    {
        var m = V("m"); var size = Add(Mul(D(3), m), D(3)); var vertices = Call("Fin", size);
        var graph = Path(size); var target = V("Hex"); var g = V("g");
        var i = V("i"); var j = V("j"); var p = V("p");
        var radius = Div(Mul(D(4), Call("real", m)), Add(Mul(D(3), Call("real", m)), D(4)));
        var edge = Some("i", vertices, Some("j", vertices, And(Call("Adj", graph, i, j),
            Le(radius, Call("err", g, p, i, j)))));
        return All("m", Naturals, Imp(Le(D(1), m), Some("g", Arrow(vertices, Arrow(vertices, target)),
            And(Call("skew", vertices, g), And(Call("flat", graph, g, D(1)), All("p", Arrow(vertices, target), edge)))));
    }
}
