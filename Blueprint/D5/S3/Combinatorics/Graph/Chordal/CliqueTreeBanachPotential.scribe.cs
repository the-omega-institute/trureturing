using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class CliqueTreeBanachPotentialDocument : IScribeDocumentDefinition
{
    private const string Path = "D5/S3/Combinatorics/Graph/Chordal/CliqueTreeBanachPotential";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Potential reconstruction on finite clique trees.",
        H("Gain reconstruction on clique trees"),
        Blocks(
            Describe.Lean(DescribeId.Create("clique-tree-center-extension"),
                DeclarationHandle.Create(Path + ".cliqueTree_center_extension_banach_potential"),
                H("Center extension"), StatementSource.FromAuthor(Disp(CenterStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A clique tree consists of a tree T and clique bags K that cover every vertex and edge of G. Every bag on a tree path between two occurrences of a vertex contains that vertex. The separator of adjacent bags is their intersection. The functions dist and ncard denote graph distance and finite cardinality.")),
                    Paragraph(Text("Start with radius coefficient one on a central clique or central edge. On one clique the mean of all its stars has the sharper local coefficient one minus two divided by its size on every edge. On a central edge, average the stars from the shared separator to obtain the coefficient one on both bags.")),
                    Paragraph(Text("Extend the potential into each successive layer by averaging the candidates obtained by extending the old values at the parent separator along an edge. When one endpoint of an edge is old, its own candidate has zero error. Each other candidate costs at most the old residual plus one triangle defect. The recurrence takes the maximum of the old coefficient, one for edges with two new endpoints, and the mixed-edge coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("clique-tree-two-clique-midpoint"),
                DeclarationHandle.Create(Path + ".cliqueTree_twoClique_midpoint_banach_potential"),
                H("Gluing at separator midpoints"), StatementSource.FromAuthor(Disp(MidpointStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For adjacent bags the separator coefficient is the product of one minus the reciprocal of the separator size and one minus the separator size divided by the larger bag size. The midpoint coefficient is the largest sum of the clique star coefficient and the two largest incident separator coefficients, padding missing terms with zero. A graph without edges has coefficient zero.")),
                    Paragraph(Text("Translate the clique means so their difference on each separator has mean zero. In the difference of the two star residuals, the common triangle term from each shared star cancels with weight equal to the reciprocal of the larger clique size. Taking the mean of the remaining increments and dropping the zero diagonal term yields the separator coefficient for the midpoint displacement.")),
                    Paragraph(Text("An edge with both endpoints in a single separator has the averaged residual of its two cliques. When the endpoints lie in different separators, their shifts are bounded by the two largest distinct incident coefficients. The finite maximum of the resulting local coefficients is strictly below three."))),
                DescribeRole.Theorem))));

    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Par(a), op, Par(b));
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Both(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Le(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Instance(string name, params Formula[] args) =>
        Seq(OpenBracket, Call(name, args), CloseBracket, Comma, Sp);

    private static Formula Graphs(Formula body)
    {
        var V = F.Id("V");
        var I = F.Id("I");
        var T = F.Id("T");
        var G = F.Id("G");
        var K = F.Id("K");
        var a = F.Id("a");
        var b = F.Id("b");
        var separators = All("a", I, All("b", I, Imp(Call("Adj", T, a, b),
            Call("Nonempty", Call("intersection", Call("K", a), Call("K", b))))));
        var tree = Imp(Call("IsCliqueTree", T, G, K), Imp(separators, body));
        return All("u", Call("Universe"), All("v", Call("Universe"), All("w", Call("Universe"),
            All("V", Call("Type", F.Id("u")), Seq(Instance("Finite", V),
                All("I", Call("Type", F.Id("w")), Seq(Instance("Finite", I),
                    All("T", Call("SimpleGraph", I), All("G", Call("SimpleGraph", V),
                        All("K", Arrow(I, Call("Set", V)), tree))))))))));
    }

    private static Formula Gains(Formula coefficient, bool strict)
    {
        var V = F.Id("V");
        var E = F.Id("E");
        var G = F.Id("G");
        var u = F.Id("x");
        var v = F.Id("y");
        var t = F.Id("t");
        var eps = F.Id("epsilon");
        Formula Adj(Formula a, Formula b) => Call("Adj", G, a, b);
        Formula Gain(Formula a, Formula b) => Call("g", a, b);
        Formula Pot(Formula a) => Call("phi", a);
        var skew = All("x", V, All("y", V,
            Rel(Gain(v, u), FormulaRelationOperator.Equal, Seq(Minus, Gain(u, v)))));
        var flat = All("t", V, All("x", V, All("y", V,
            Imp(Adj(t, u), Imp(Adj(u, v), Imp(Adj(t, v),
                Le(Call("norm", Sub(Seq(Gain(t, u), Plus, Gain(u, v)), Gain(t, v))), eps)))))));
        var result = Some("phi", Arrow(V, E), All("x", V, All("y", V, Imp(Adj(u, v),
            Le(Call("norm", Sub(Gain(u, v), Par(Sub(Pot(v), Pot(u))))),
                Seq(coefficient, Sp, Cdot, Sp, eps))))));
        if (strict)
            result = Both(Rel(coefficient, FormulaRelationOperator.LessThan, D(3)), result);
        return All("E", Call("Type", F.Id("v")), Seq(
            Instance("SeminormedAddCommGroup", E), Instance("NormedSpace", R, E),
            All("g", Arrow(V, Arrow(V, E)), All("epsilon", R,
                Imp(Le(D(0), eps), Imp(skew, Imp(flat, result)))))));
    }

    private static Formula CenterStatement()
    {
        var I = F.Id("I");
        var T = F.Id("T");
        var a = F.Id("a");
        var b = F.Id("b");
        var m = F.Id("m");
        var diameter = F.Id("D");
        var sizes = All("a", I, All("b", I, Imp(Call("Adj", T, a, b),
            Le(Call("ncard", Call("intersection", Call("K", a), Call("K", b))), m))));
        var diam = All("a", I, All("b", I, Le(Call("dist", T, a, b), diameter)));
        var radius = Call("cliqueTreeRadius", m, D(1), Call("natDiv", diameter, D(2)));
        return Graphs(All("m", N, Imp(Le(D(1), m), Imp(sizes, All("D", N,
            Imp(diam, Gains(radius, false)))))));
    }

    private static Formula MidpointStatement()
    {
        var I = F.Id("I");
        var V = F.Id("V");
        var x = F.Id("x");
        var occurrences = Call("fiberMembership", F.Id("K"), x, I);
        return Graphs(Imp(All("x", V, Le(Call("ncard", occurrences), D(2))),
            Gains(Call("cliqueTreeMidpointCoeff", F.Id("T"), F.Id("K")), true)));
    }
}
