using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class MultiIdentitySimplicialBanachDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Chordal/MultiIdentitySimplicialBanach.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Old triangle differences and two retained identities bound chordal gain residuals.",
        H("Chordal reconstruction by retained simplicial identities"),
        Blocks(
            Describe.Lean(DescribeId.Create("old-triangle-regrouped-reconstruction"),
                DeclarationHandle.Create(Prefix + "exists_regrouped_simplicial_banach_gain_potential"),
                H("Old triangle regrouping"), StatementSource.FromAuthor(Disp(Regrouped())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Reverse a perfect elimination order so that each earlier neighborhood is a clique. Assign each potential by averaging the earlier potentials plus their gains into the new vertex. The weights are uniform below k predecessors. At k predecessors, the first k minus one weights are s and the last is t, where s is the reciprocal of one plus R and the weights sum to one.")),
                    Paragraph(Text("The retained weighted residual at each vertex is zero. For the edge from the newest predecessor of a full neighborhood, its own earlier clique contains the other predecessors. If it contains one extra vertex, subtract its retained identity and pair the residual at that extra vertex with the residual at its newest predecessor. The old triangle bounds the difference by R plus one times epsilon. This gives the quadratic closing condition. The operator real denotes the natural-number cast."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("two-identity-clique-six-reconstruction"),
                DeclarationHandle.Create(Prefix + "exists_multiIdentity_cliqueSix_banach_gain_potential"),
                H("Two identities for clique size six"), StatementSource.FromAuthor(Disp(
                    Chordal(Imp(CliqueBound(D(6)), Gains(Sub(Mul(D(2), Call("sqrt", D(3))), D(1))))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Average uniformly for at most three predecessors. For four or five, use weights s, s, s, t followed by zeros. Here s is the reciprocal of two times the square root of three and t is one minus three times s.")),
                    Paragraph(Text("In the exceptional edge of weight t, the three older current predecessors include one primary vertex, the former fourth vertex and the former fifth vertex. Subtract the retained identity at the current endpoint and eliminate the residual at the former fifth vertex using its own identity. For an extra predecessor of that vertex, the auxiliary vector is the sum of the residual at the eliminated vertex and the residual from that vertex to its extra predecessor. The auxiliary distances and shared triangle defects together cost the coefficient used in the elimination."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("two-identity-clique-seven-reconstruction"),
                DeclarationHandle.Create(Prefix + "exists_multiIdentity_cliqueSeven_banach_gain_potential"),
                H("Two identities for clique size seven"), StatementSource.FromAuthor(Disp(
                    Chordal(Imp(CliqueBound(D(7)), Gains(Div(Add(D(3), Call("sqrt", D(7))), D(2))))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Use the three equal leading weights s, then t, then zeros in predecessor cliques of size four through six. For the two exceptional edges of weight t, eliminate the contribution from the last vertex of the old six-vertex predecessor clique by its retained identity.")),
                    Paragraph(Text("The decisive edge has weight zero and omits two primary vertices of its earlier clique. Eliminate the contribution of its newest predecessor with coefficient t. The resulting negative mass is at most twice s minus t times s plus t, with the latter product subtracted as a whole. The bound closes by the quadratic equation for the displayed radius."))),
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
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Inst(string name, params Formula[] args) =>
        Seq(OpenBracket, Call(name, args), CloseBracket, Comma, Sp);

    private static Formula Gains(Formula coefficient)
    {
        var vertices = V("V"); var graph = V("G"); var target = V("E");
        var u = V("i"); var v = V("j"); var w = V("l"); var eps = V("epsilon");
        Formula Gain(Formula a, Formula b) => Call("g", a, b);
        Formula Adj(Formula a, Formula b) => Call("Adj", graph, a, b);
        var skew = All("i", vertices, All("j", vertices, Eq(Gain(v, u), Seq(Minus, Gain(u, v)))));
        var tri = All("i", vertices, All("j", vertices, All("l", vertices,
            Imp(Adj(u, v), Imp(Adj(v, w), Imp(Adj(u, w),
                Le(Call("norm", Sub(Add(Gain(u, v), Gain(v, w)), Gain(u, w))), eps)))))));
        var err = Call("norm", Sub(Gain(u, v), Par(Sub(Call("phi", v), Call("phi", u)))));
        var fit = Some("phi", Arrow(vertices, target),
            All("i", vertices, All("j", vertices, Imp(Adj(u, v), Le(err, Mul(Par(coefficient), eps))))));
        return All("E", Call("Type", V("v")), Seq(Inst("SeminormedAddCommGroup", target),
            Inst("NormedSpace", R, target), All("g", Arrow(vertices, Arrow(vertices, target)),
                All("epsilon", R, Imp(Le(D(0), eps), Imp(skew, Imp(tri, fit)))))));
    }

    private static Formula CliqueBound(Formula bound) =>
        All("C", Call("Set", V("V")),
            Imp(Call("IsClique", V("G"), V("C")), Le(Call("ncard", V("C")), bound)));

    private static Formula Chordal(Formula body)
    {
        var vertices = V("V"); var graph = V("G");
        var universal = All("V", Call("Type", V("u")), Seq(Inst("Finite", vertices),
            All("G", Call("SimpleGraph", vertices), Imp(Call("IsChordal", graph), body))));
        return All("u", Call("Universe"), All("v", Call("Universe"), universal));
    }

    private static Formula Regrouped()
    {
        var k = V("k"); var radius = V("radius"); var realK = Call("real", k);
        var bounds = Imp(Le(Call("max", D(1), Sub(realK, D(2))), radius),
            Imp(Le(radius, Sub(realK, D(1))),
                Imp(Le(Mul(D(2), Par(Sub(realK, D(1)))), Mul(radius, Par(Add(radius, D(1))))),
                    Gains(radius))));
        return Chordal(All("k", N, Imp(Le(D(2), k),
            Imp(CliqueBound(Add(k, D(1))), All("radius", R, bounds)))));
    }
}
