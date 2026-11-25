using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal;

internal sealed class MultiTierAndUniversalCliqueBanachDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharper gain reconstruction from predecessor sizes and universal cores.",
        H("Multi-tier and universal-core gain potentials"),
        Blocks(
            Describe.Lean(DescribeId.Create("multitier-clique-banach-gain-potential"),
                DeclarationHandle.Create(Path + ".exists_multitier_clique_banach_gain_potential"),
                H("Multi-tier predecessor averaging"), StatementSource.FromAuthor(Disp(PredecessorStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The function real casts a natural number to a real, toSet takes the underlying set of a finset, and norm denotes the seminorm of E.")),
                    Paragraph(Text("Root each connected component. In any predecessor clique, the vertices with at least s predecessors themselves have nested predecessor sets. If that collection is nonempty, its union with a smallest common predecessor set is a disjoint clique. Thus the collection has at most k + 1 − s vertices.")),
                    Paragraph(Text("Use the profile 1/n for positive sizes n up to k − 2, and use the two smaller values (k − 2)/D and (k − 3)/D at k − 1 and k, where D is k squared minus 3k plus 3. A row gives each predecessor at least the row profile and at least twice the middle profile minus that predecessor's own profile. The counts at thresholds k and k − 1 bound the total preliminary weight by one. Distribute any unused weight uniformly.")),
                    Paragraph(Text("Transport along the shadow anchors and average the paths through the predecessors. Across layers, the reference path has a matching term in each mean, and their combined weights save twice the middle profile in distinguished mass. Within a layer, each predecessor in the smaller clique has a matching term in the larger clique. Its error costs one triangle defect and every other term costs at most three. For k equal to four the resulting coefficient is 20/7."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("universal-core-simplicial-banach-potential"),
                DeclarationHandle.Create(Path + ".exists_universal_core_simplicial_banach_potential"),
                H("Simplicial attachments to a universal core"), StatementSource.FromAuthor(Disp(CoreStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The set neighbors(G, o) consists of the vertices adjacent to o. Here ncard counts a finite set and complement is relative to V.")),
                    Paragraph(Text("On the core H, average the gains from all universal vertices in U. Every residual on a core edge is an average of triangle defects with zero contributions from any endpoints in U.")),
                    Paragraph(Text("For an outside vertex o with neighbors, average the candidate values obtained by extending the potential from each neighbor along its edge to o. The candidates of two distinct neighbors differ by at most twice the tolerance, from the core edge residual and the triangle through o. The self-term vanishes, giving the factor 2 − 2 divided by the number of neighbors. An isolated outside vertex receives zero."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bridged-gadget-banach-upper-bound"),
                DeclarationHandle.Create(Path + ".bridgedGadget_banach_upper_bound"),
                H("Reconstruction on the bridged gadget"), StatementSource.FromAuthor(Disp(GadgetStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("In each copy, remove the root to obtain the core and take the u-clique as its universal set. The root attaches to the m-clique of a-vertices, so the core extension gives the coefficient 2 − 2/m.")),
                    Paragraph(Text("Translate each copy by a common potential increment determined by the gains on the preceding root bridges. The translation preserves intra-copy residuals and gives zero residual on every bridge."))),
                DescribeRole.Theorem))));

    private const string Path = "D5/S3/Combinatorics/Graph/Chordal/MultiTierAndUniversalCliqueBanach";
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
    private static Formula InSet(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Subset(Formula a, Formula b) => Rel(a, FormulaRelationOperator.SubsetOf, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Minus, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Cdot, Sp, b);
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Instance(string name, params Formula[] args) =>
        Seq(OpenBracket, Call(name, args), CloseBracket, Sp);

    private static Formula Reconstruction(Formula vertices, Formula graph, Formula coefficient)
    {
        var space = F.Id("E");
        var i = F.Id("i");
        var j = F.Id("j");
        var l = F.Id("l");
        var eps = F.Id("epsilon");
        Formula adj(Formula a, Formula b) => Call("Adj", graph, a, b);
        Formula gain(Formula a, Formula b) => Call("g", a, b);
        Formula pot(Formula a) => Call("phi", a);
        var skew = All("i", vertices, All("j", vertices,
            Rel(gain(j, i), FormulaRelationOperator.Equal, Seq(Minus, gain(i, j)))));
        var triangle = All("i", vertices, All("j", vertices, All("l", vertices,
            Imp(adj(i, j), Imp(adj(j, l), Imp(adj(i, l),
                Le(Call("norm", Sub(Seq(gain(i, j), Plus, gain(j, l)), gain(i, l))), eps)))))));
        var result = Some("phi", Arrow(vertices, space),
            All("i", vertices, All("j", vertices, Imp(adj(i, j),
                Le(Call("norm", Sub(gain(i, j), Par(Sub(pot(j), pot(i))))), Mul(Par(coefficient), eps))))));
        return All("E", Call("Type", F.Id("v")), Seq(
            Instance("SeminormedAddCommGroup", space), Instance("NormedSpace", R, space), Comma, Sp,
            All("g", Arrow(vertices, Arrow(vertices, space)), All("epsilon", R,
                Imp(Le(D(0), eps), Imp(skew, Imp(triangle, result)))))));
    }

    private static Formula FiniteGraph(Formula body)
    {
        var vertices = F.Id("V");
        return All("u", Call("Universe"), All("v", Call("Universe"),
            All("V", Call("Type", F.Id("u")), Seq(Instance("Finite", vertices), Comma, Sp,
                All("G", Call("SimpleGraph", vertices), body)))));
    }

    private static Formula PredecessorStatement()
    {
        var vertices = F.Id("V");
        var graph = F.Id("G");
        var k = F.Id("k");
        var s = F.Id("s");
        var rk = Call("real", k);
        var clique = All("s", Call("Finset", vertices), Imp(Call("IsClique", graph, Call("toSet", s)),
            Le(Call("card", s), Seq(k, Plus, D(1)))));
        var denominator = Seq(Sub(new Formula.Power(rk, D(2)), Mul(D(3), rk)), Plus, D(3));
        var coefficient = Sub(D(4), Div(Mul(D(4), Par(Sub(rk, D(2)))), denominator));
        return FiniteGraph(Imp(Call("IsChordal", graph), All("k", N,
            Imp(Le(D(4), k), Imp(clique, Reconstruction(vertices, graph, coefficient))))));
    }

    private static Formula CoreStatement()
    {
        var vertices = F.Id("V");
        var graph = F.Id("G");
        var core = F.Id("H");
        var universal = F.Id("U");
        var m = F.Id("m");
        var u = F.Id("u");
        var h = F.Id("h");
        var o = F.Id("o");
        var outside = Call("complement", core);
        var neighbors = Call("neighbors", graph, o);
        var universalAdj = All("u", vertices, Imp(InSet(u, universal),
            All("h", vertices, Imp(InSet(h, core),
                Imp(Rel(u, FormulaRelationOperator.NotEqual, h), Call("Adj", graph, u, h))))));
        var attachment = All("o", vertices, Imp(InSet(o, outside),
            Both(Subset(neighbors, core), Both(Call("IsClique", graph, neighbors),
                Le(Call("ncard", neighbors), m)))));
        var coefficient = Call("max", D(1), Sub(D(2), Div(D(2), Call("real", m))));
        var result = All("m", N, Imp(Le(D(1), m),
            Imp(attachment, Reconstruction(vertices, graph, coefficient))));
        return FiniteGraph(All("H", Call("Set", vertices), All("U", Call("Set", vertices),
            Imp(Subset(universal, core), Imp(Call("Nonempty", universal),
                Imp(universalAdj, Imp(Call("IsIndepSet", graph, outside), result)))))));
    }

    private static Formula GadgetStatement()
    {
        var m = F.Id("m");
        var n = F.Id("N");
        var vertices = Seq(Call("Fin", n), Sp, Times, Sp, Call("GadgetVertex", m));
        var graph = Call("bridgedGadget", m, n);
        var coefficient = Sub(D(2), Div(D(2), Call("real", m)));
        return All("v", Call("Universe"), All("m", N, All("N", N,
            Imp(Le(D(2), m), Imp(Le(D(1), n), Reconstruction(vertices, graph, coefficient))))));
    }
}

