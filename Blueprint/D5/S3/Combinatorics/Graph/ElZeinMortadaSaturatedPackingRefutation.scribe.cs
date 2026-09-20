using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ElZeinMortadaSaturatedPackingRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/ElZeinMortadaSaturatedPackingRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/elzein2026local");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A connected seven-vertex graph refutes the printed saturated-subcubic packing conjecture.",
        H("A Seven-Vertex Saturated Packing Refutation"),
        Blocks(
            Node("subcubic-definition", "Subcubic graphs", "Subcubic", SubcubicFormula(),
                "A finite simple graph is subcubic exactly when every vertex has degree at "
                    + "most three.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("saturated-definition", "Saturated subcubic graphs", "Saturated",
                SaturatedFormula(),
                "For a natural number k, saturation requires each degree-three vertex to "
                    + "have at most k neighbours that also have degree three. The displayed "
                    + "filtered neighbour set is the defining expression.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("packing-definition", "The (1,1,2)-packing condition", "IsPacking112",
                PackingFormula(),
                "The fibres of c partition V into three classes, including the possibility "
                    + "of empty classes. Equal colors zero and one require extended distance "
                    + "greater than one, while color two requires extended distance greater "
                    + "than two. Extended distance is infinity across distinct components; "
                    + "ordinary SimpleGraph.dist instead returns zero when no path exists, "
                    + "which would not express the graph-distance convention for disconnected graphs.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("printed-conjecture-three", "The printed Conjecture 3", "claim",
                ClaimFormula(),
                "The source definitions read verbatim: \"A graph G is said to be subcubic if "
                    + "∆(G) ≤ 3 […].\" \"A subcubic graph is said to be k-saturated, for "
                    + "0 ≤ k ≤ 3, if every vertex of degree 3 is adjacent to at most k vertices "
                    + "of degree 3.\" \"Given a non-decreasing sequence of positive integers "
                    + "S = (s₁, s₂, …, s_k), an S-packing coloring of a graph G is a partition "
                    + "of V(G) into subsets V₁, V₂, …, V_k such that for any two distinct "
                    + "vertices u, v ∈ V_i, we have dist_G(u, v) > s_i.\" Conjecture 3 reads "
                    + "verbatim: \"Every 2-saturated subcubic graph is (1, 1, 2)-packing "
                    + "colorable.\" The displayed conjecture has no local-girth hypothesis. "
                    + "The quantified type V is in universe zero, so claim is a closed proposition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("printed-conjecture-three-refuted", "Conjecture 3 is false", "result",
                ResultFormula(),
                "The graph with graph6 encoding FhcYG has edges 01, 04, 12, 16, 23, 34, "
                    + "35, 45, and 56. Its degree sequence is 2,3,2,3,3,3,2, and its four "
                    + "degree-three vertices have 0,2,2,2 degree-three neighbours. The triangle "
                    + "on 3,4,5 forces one triangle vertex into color two. Every vertex is at "
                    + "extended distance at most two from each triangle vertex, so no other "
                    + "vertex can have color two. Deleting 3, 4, or 5 leaves respectively the "
                    + "five-cycles 0-1-6-5-4-0, 1-2-3-5-6-1, or 0-1-2-3-4-0. The remaining "
                    + "six vertices therefore cannot be split between the two independent "
                    + "radius-one classes.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo())),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role);

    private static Formula SubcubicFormula()
    {
        var vType = F.Id("V");
        var graph = F.Id("G");
        var vertex = F.Id("v");
        var body = Universal("v", vType,
            LessEqual(Call("degree", graph, vertex), D(3)));
        return Disp(TypeAndGraphBinders(vType, graph,
            Iff(Call("Subcubic", graph), body), decidableEquality: false));
    }

    private static Formula SaturatedFormula()
    {
        var vType = F.Id("V");
        var graph = F.Id("G");
        var vertex = F.Id("v");
        var neighbor = F.Id("u");
        var k = F.Id("k");
        var degreeThreeNeighbors = SetBuilder(
            Seq(Typed(neighbor, vType), Sp, InMacro, Sp, Call("neighborFinset", graph, vertex)),
            Equal(Call("degree", graph, neighbor), D(3)));
        var body = Universal("v", vType, Implies(
            Equal(Call("degree", graph, vertex), D(3)),
            LessEqual(Call("card", degreeThreeNeighbors), k)));
        return Disp(Universal("V", Type(), Implies(
            And(Call("Fintype", vType), Call("DecidableEq", vType)),
            Universal("k", Naturals(),
                Universal("G", Call("SimpleGraph", vType), Implies(
                    Call("DecidableRel", Call("Adj", graph)),
                    Iff(Call("Saturated", k, graph), body)))))));
    }

    private static Formula PackingFormula()
    {
        var vType = F.Id("V");
        var graph = F.Id("G");
        var coloring = F.Id("c");
        var u = F.Id("u");
        var v = F.Id("v");
        var colorType = Call("Fin", D(3));
        var sameColor = Equal(Call("c", u), Call("c", v));
        var separated = Call("if",
            Equal(Call("c", u), D(2)),
            Less(Typed(D(2), ExtendedNaturals()), Call("edist", graph, u, v)),
            Less(Typed(D(1), ExtendedNaturals()), Call("edist", graph, u, v)));
        var body = Exists("c", Arrow(vType, colorType),
            Universal("u", vType, Universal("v", vType,
                Implies(NotEqual(u, v), Implies(sameColor, separated)))));
        return Disp(Universal("V", Type(),
            Universal("G", Call("SimpleGraph", vType),
                Iff(Call("IsPacking112", graph), body))));
    }

    private static Formula ClaimFormula()
    {
        var vType = F.Id("V");
        var graph = F.Id("G");
        var conclusion = Implies(Call("Subcubic", graph),
            Implies(Call("Saturated", D(2), graph),
                Call("IsPacking112", graph)));
        var quantified = TypeAndGraphBinders(vType, graph, conclusion, decidableEquality: true);
        return Disp(Iff(F.Id("claim"), quantified));
    }

    private static Formula ResultFormula() => Disp(new Formula.Not(F.Id("claim")));

    private static Formula TypeAndGraphBinders(
        Formula vType, Formula graph, Formula body, bool decidableEquality)
    {
        Formula withGraph = Universal("G", Call("SimpleGraph", vType), Implies(
            Call("DecidableRel", Call("Adj", graph)), body));
        if (decidableEquality)
            withGraph = Implies(Call("DecidableEq", vType), withGraph);
        return Universal("V", Type(),
            Implies(Call("Fintype", vType), withGraph));
    }

    private static Formula Type() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Type"));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula ExtendedNaturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("ENat"));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(Parenthesized(domain), Sp, To, Sp, Parenthesized(codomain));

    private static Formula SetBuilder(Formula binder, Formula predicate) =>
        Seq(OpenBrace, binder, Sp, Mid, Sp, predicate, CloseBrace);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
