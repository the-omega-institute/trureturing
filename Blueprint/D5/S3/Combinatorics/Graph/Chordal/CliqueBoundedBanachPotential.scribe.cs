using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class CliqueBoundedBanachPotentialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Averaging over the predecessors gives a uniform error bound depending on the clique number.",
        H("Averaged gain reconstruction on chordal graphs"),
        Blocks(Describe.Lean(
            DescribeId.Create("clique-bounded-banach-gain-potential"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Chordal/CliqueBoundedBanachPotential.exists_clique_bounded_banach_gain_potential"),
            H("The clique-bounded reconstruction estimate"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("In the statement, toSet takes the underlying set of a finite set, real casts a natural number to a real, and norm is the seminorm on E.")),
                Paragraph(Text("Choose a root in each connected component and partition its vertices into distance layers. For a component of the subgraph at or above a fixed layer, its shadow is the clique of its neighbors in the preceding layer. Above the first layer, a common predecessor of the entire shadow extends it by one vertex to a clique. Thus every predecessor set has at most k vertices. In the first layer the predecessor set is the root alone.")),
                Paragraph(Text("Transport the potential along the chain of common predecessors used as anchors. At each vertex add the mean of the gains along the two-edge paths from its anchor through its predecessors. The root has potential zero and the first-layer edges from the root have zero residual.")),
                Paragraph(Text("Across consecutive layers, compare through the later component's anchor. On each side, one predecessor gives the reference path exactly. Each other term uses at most two triangle comparisons. The norm of each mean difference is therefore at most two times the triangle tolerance times one minus the reciprocal of the predecessor count. Adding both bounds gives the stated coefficient.")),
                Paragraph(Text("For adjacent vertices in the same layer, chordality orders their predecessor sets by inclusion. Fix a predecessor from the smaller set and average against the larger set. The matching predecessor costs one triangle comparison, and each distinct predecessor costs at most three. Averaging over the smaller set preserves the bound of three minus two divided by k, which is at most the stated coefficient for k at least two.")),
                Paragraph(Text("Each connected component has its own potential. The coefficient is eight thirds for k equal to three and three for k equal to four."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(Par(premise), FormulaLogicOperator.Implies, Par(conclusion));
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Instance(string name, params Formula[] args) =>
        Seq(OpenBracket, Call(name, args), CloseBracket, Sp);

    private static Formula Statement()
    {
        var vertices = F.Id("V");
        var graph = F.Id("G");
        var space = F.Id("E");
        var width = F.Id("k");
        var s = F.Id("s");
        var i = F.Id("i");
        var j = F.Id("j");
        var l = F.Id("l");
        var eps = F.Id("epsilon");
        var reals = Seq(Mathbb, Grp(F.Id("R")));
        var naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula adj(Formula a, Formula b) => Call("Adj", graph, a, b);
        Formula gain(Formula a, Formula b) => Call("g", a, b);
        Formula pot(Formula a) => Call("phi", a);

        var clique = All("s", Call("Finset", vertices),
            Imp(Call("IsClique", graph, Call("toSet", s)), Le(Call("card", s), Seq(width, Plus, D(1)))));
        var reversal = All("i", vertices, All("j", vertices,
            new Formula.Relation(gain(j, i), FormulaRelationOperator.Equal, Seq(Minus, gain(i, j)))));
        var triangle = All("i", vertices, All("j", vertices, All("l", vertices,
            Imp(adj(i, j), Imp(adj(j, l), Imp(adj(i, l),
                Le(Call("norm", Sub(Seq(gain(i, j), Plus, gain(j, l)), gain(i, l))), eps)))))));
        var coefficient = Sub(D(4), Seq(Frac, Grp(D(4)), Grp(Call("real", width))));
        Formula result = Some("phi", Arrow(vertices, space),
            All("i", vertices, All("j", vertices, Imp(adj(i, j),
                Le(Call("norm", Sub(gain(i, j), Par(Sub(pot(j), pot(i))))),
                    Seq(Par(coefficient), Sp, Cdot, Sp, eps))))));
        result = All("g", Arrow(vertices, Arrow(vertices, space)),
            All("epsilon", reals, Imp(Le(D(0), eps), Imp(reversal, Imp(triangle, result)))));
        result = All("E", Call("Type", F.Id("v")), Seq(
            Instance("SeminormedAddCommGroup", space), Instance("NormedSpace", reals, space),
            Comma, Sp, result));
        result = All("k", naturals, Imp(Le(D(2), width), Imp(clique, result)));
        result = All("V", Call("Type", F.Id("u")), Seq(Instance("Finite", vertices), Comma, Sp,
            All("G", Call("SimpleGraph", vertices), Imp(Call("IsChordal", graph), result))));
        return All("u", Call("Universe"), All("v", Call("Universe"), result));
    }
}
