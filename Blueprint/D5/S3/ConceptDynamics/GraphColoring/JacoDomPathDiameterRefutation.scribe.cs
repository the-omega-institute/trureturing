using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.GraphColoring;

internal sealed class JacoDomPathDiameterRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/kok2025jaco");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite linear Jaco graph on 33 vertices refutes Kok's dom-path diameter conjecture.",
        H("A Dom-Path Longer Than the Jaco Graph Diameter Bound"),
        Blocks(
            Node("jaco-vertex", "One-indexed Jaco vertices", "Vertex", VertexFormula(),
                "Vertex n is the subtype of natural indices from 1 through n. This preserves "
                    + "the paper's labels v_1 through v_n rather than shifting them to zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("finite-jaco-graph", "The finite linear Jaco graph", "jaco", JacoFormula(),
                "The graph jaco n restricts the frozen infinite Jaco adjacency to the "
                    + "one-indexed vertices through n. Truncation removes only neighbors whose "
                    + "indices exceed n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("walk-vertex-positions", "Positions occupied by a vertex set", "positions",
                PositionsFormula(),
                "For a walk w and vertex set D, positions w D contains exactly the indices "
                    + "whose walk vertices lie in D. Its carrier has w.length + 1 elements.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("jaco-dom-path", "Dom-paths", "IsDomPath", IsDomPathFormula(),
                "A dom-path is a simple walk from v_1 to v_n with one set D of walk vertices. "
                    + "The positions of D form a minimum dominating set of the path graph, and "
                    + "the same D is a minimum dominating set of the finite Jaco graph.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("jaco-dom-path-diameter-claim", "Kok's Conjecture 2.9", "claim",
                ClaimFormula(),
                "For every positive n, the conjectured bound requires some dom-path whose "
                    + "edge length is at most the Mathlib diameter of jaco n plus one. This "
                    + "existential statement is the weakest consequence independent of how "
                    + "the source selects its primary minimal dom-path.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("jaco-dom-path-diameter-refuted", "Conjecture 2.9 is false", "result",
                ResultFormula(),
                "At n = 33 every dominating set has at least four vertices, while a path on "
                    + "at most nine vertices has domination number at most three. The graph "
                    + "diameter is at most seven, so any path allowed by the conjectured bound "
                    + "would have at most nine vertices, giving a contradiction. A ten-vertex "
                    + "dom-path exists, so the contradiction is not caused by an empty notion.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

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

    private static Formula VertexFormula()
    {
        var n = F.Id("n");
        var i = F.Id("i");
        var interval = SetBuilder(Typed(i, Naturals()),
            And(LessEqual(D(1), i), LessEqual(i, n)));
        return Disp(Bound("n", Naturals(), Equal(Call("Vertex", n), interval)));
    }

    private static Formula JacoFormula()
    {
        var n = F.Id("n");
        var a = F.Id("a");
        var b = F.Id("b");
        var vertex = Call("Vertex", n);
        var adjacency = Iff(
            Call("Adj", Call("jaco", n), a, b),
            Call("Adj", Call("val", a), Call("val", b)));
        return Disp(Bound("n", Naturals(),
            Bound("a", vertex, Bound("b", vertex, adjacency))));
    }

    private static Formula PositionsFormula()
    {
        var n = F.Id("n");
        var u = F.Id("u");
        var v = F.Id("v");
        var w = F.Id("w");
        var d = F.Id("D");
        var i = F.Id("i");
        var vertex = Call("Vertex", n);
        var graph = Call("jaco", n);
        var walk = Call("Walk", graph, u, v);
        var positionType = Call("Fin", Add(Call("length", w), D(1)));
        var selected = SetBuilder(Typed(i, positionType),
            Member(Call("getVert", w, i), d));
        return Disp(Bound("n", Naturals(), Bound("u", vertex, Bound("v", vertex,
            Bound("w", walk, Bound("D", Call("Finset", vertex),
                Equal(Call("positions", w, d), selected)))))));
    }

    private static Formula IsDomPathFormula()
    {
        var n = F.Id("n");
        var h = F.Id("h");
        var w = F.Id("w");
        var d = F.Id("D");
        var graph = Call("jaco", n);
        var vertexType = Call("Vertex", n);
        var first = Parenthesized(Typed(D(1), vertexType));
        var last = Parenthesized(Typed(n, vertexType));
        var path = Call("pathGraph", Add(Call("length", w), D(1)));
        var walk = Call("Walk", graph, first, last);
        var body = Iff(Call("IsDomPath", n, h, w),
            And(
                Call("IsPath", w),
                Exists("D", Call("Finset", vertexType),
                    And(
                        SubsetOf(d, Call("toFinset", Call("support", w))),
                        Call("IsNDominatingSet", path, Call("dominationNumber", path),
                            Call("positions", w, d)),
                        Call("IsNDominatingSet", graph, Call("dominationNumber", graph), d)))));
        return Disp(Bound("n", Naturals(),
            Bound("h", LessEqual(D(1), n), Bound("w", walk, body))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var h = F.Id("h");
        var w = F.Id("w");
        var graph = Call("jaco", n);
        var vertexType = Call("Vertex", n);
        var first = Parenthesized(Typed(D(1), vertexType));
        var last = Parenthesized(Typed(n, vertexType));
        var walk = Call("Walk", graph, first, last);
        var conclusion = Exists("w", walk,
            And(
                Call("IsDomPath", n, h, w),
                LessEqual(Call("length", w), Add(Call("diam", graph), D(1)))));
        var quantified = Bound("n", Naturals(),
            Bound("h", LessEqual(D(1), n), conclusion));
        return Disp(Iff(F.Id("claim"), quantified));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula SetBuilder(Formula binder, Formula predicate) =>
        Seq(OpenBrace, binder, Sp, Mid, Sp, predicate, CloseBrace);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Bound(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);

    private static Formula SubsetOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        return result;
    }
}
