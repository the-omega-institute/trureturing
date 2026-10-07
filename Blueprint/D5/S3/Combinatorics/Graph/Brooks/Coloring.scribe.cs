using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Brooks;

internal sealed class ColoringDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Brooks/Coloring.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Greedy ordering colors a connected subcubic graph with a low-degree vertex; compatible colorings also extend across a vertex or glue along a cut.",
        H("Greedy Coloring and Vertex Extensions"),
        Blocks(
            Paragraph(Text(
                "A coloring with n colors assigns an element of Fin n to each vertex and gives "
                + "different colors to adjacent vertices. Degree counts neighbors, not an average "
                + "over vertices. Induce(G,S) denotes the graph induced on S; sets and finite sets "
                + "are interpreted as vertex subsets when used in this notation.")),
            Describe.Lean(DescribeId.Create("connected-low-degree"),
                DeclarationHandle.Create(Prefix + "connected_colorable_three_of_exists_degree_lt"),
                H("A Low-Degree Vertex in a Connected Subcubic Graph"),
                StatementSource.FromAuthor(ConnectedFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
                Blocks(Paragraph(Text(
                    "Let G be a simple graph on a finite vertex type, with decidable adjacency. "
                    + "If G is connected, every vertex has degree at most three, and some vertex "
                    + "has degree below three, then G is three-colorable. Order vertices by "
                    + "decreasing distance from the chosen low-degree vertex, with an injective "
                    + "tie-breaker. Every other vertex has a closer neighbor still to be colored, "
                    + "so fewer than three already colored neighbors restrict its choice. "
                    + "The root also has fewer than three neighbors. Connectedness includes "
                    + "nonemptiness; the empty graph is not an instance of these premises."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("glue-at-vertex"),
                DeclarationHandle.Create(Prefix + "colorable_glue_at_vertex"),
                H("Glue Two Three-Colorings at a Vertex"),
                StatementSource.FromAuthor(GlueFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
                Blocks(Paragraph(Text(
                    "For a finite vertex type with decidable equality, let A and B cover all "
                    + "vertices and let x belong to both. Suppose no edge joins a vertex of A "
                    + "other than x to a vertex of B other than x. Three-colorings of G[A] "
                    + "and G[B] then give a three-coloring of G. Permute the colors on B to "
                    + "agree at x, and use the A-coloring wherever A applies. The assumptions "
                    + "do not require connectedness or assert that A and B intersect only at x."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("extend-after-vertex-deletion"),
                DeclarationHandle.Create(Prefix + "of_induce_compl_singleton"),
                H("Extend a Coloring over One Low-Degree Vertex"),
                StatementSource.FromAuthor(ExtensionFormula()),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/GraphInvariants/rabern2026brookslean")),
                Blocks(Paragraph(Text(
                    "Let v be a vertex of any simple graph, and assume only that its neighbor "
                    + "set is finite. If deleting v leaves an n-colorable graph and v has fewer "
                    + "than n neighbors, extend the coloring by choosing a color absent from "
                    + "those neighbors. The entire vertex type need not be finite or connected. "
                    + "The strict degree bound forces n to be positive; no extra positive-color "
                    + "premise is imposed."))),
                DescribeRole.Theorem))));

    private static Formula ConnectedFormula()
    {
        var v = F.Id("V"); var g = F.Id("G"); var x = F.Id("x");
        return Disp(All("V", Call("Type"), Instance("Fintype", v,
            All("G", Call("SimpleGraph", v), Instance("DecidableRel", Call("Adj", g),
                Implies(And(Call("Connected", g),
                    All("x", v, Rel(Call("degree", g, x), FormulaRelationOperator.LessThanOrEqual, D(3))),
                    Exists("x", v, Rel(Call("degree", g, x), FormulaRelationOperator.LessThan, D(3)))),
                    Call("Colorable", g, D(3))))))));
    }

    private static Formula GlueFormula()
    {
        var v = F.Id("V"); var g = F.Id("G"); var a = F.Id("A"); var b = F.Id("B");
        var x = F.Id("x"); var u = F.Id("u"); var w = F.Id("w");
        var cross = All("u", v, All("w", v, Implies(And(Call("Mem", u, a),
            Call("Mem", w, b), Ne(u, x), Ne(w, x)), Not(Call("Adj", g, u, w)))));
        var premises = And(Rel(Call("Union", a, b), FormulaRelationOperator.Equal, Call("Univ", v)),
            Call("Mem", x, a), Call("Mem", x, b), cross,
            Call("Colorable", Call("Induce", g, a), D(3)),
            Call("Colorable", Call("Induce", g, b), D(3)));
        return Disp(All("V", Call("Type"), Instance("Fintype", v, Instance("DecidableEq", v,
            All("G", Call("SimpleGraph", v), All("A", Call("Finset", v),
                All("B", Call("Finset", v), All("x", v,
                    Implies(premises, Call("Colorable", g, D(3)))))))))));
    }

    private static Formula ExtensionFormula()
    {
        var v = F.Id("V"); var g = F.Id("G"); var x = F.Id("x"); var n = F.Id("n");
        return Disp(All("V", Call("Type"), All("G", Call("SimpleGraph", v), All("x", v,
            All("n", Call("Nat"), Instance("Fintype", Call("neighborSet", g, x),
                Implies(And(Call("Colorable", Call("Induce", g, Call("Compl", Call("Singleton", x))), n),
                    Rel(Call("degree", g, x), FormulaRelationOperator.LessThan, n)),
                    Call("Colorable", g, n))))))));
    }

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Instance(string name, Formula arg, Formula body) =>
        Seq(OpenBracket, Call(name, arg), CloseBracket, Sp, body);
    private static Formula Rel(Formula l, FormulaRelationOperator op, Formula r) => new Formula.Relation(l, op, r);
    private static Formula Ne(Formula l, Formula r) => Rel(l, FormulaRelationOperator.NotEqual, r);
    private static Formula Not(Formula body) => Seq(Neg, Sp, Open, body, Close);
    private static Formula And(params Formula[] terms)
    {
        var result = terms[^1];
        for (var i = terms.Length - 2; i >= 0; --i)
            result = new Formula.Logic(terms[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Implies(Formula l, Formula r) =>
        new Formula.Logic(Seq(Open, l, Close), FormulaLogicOperator.Implies, Seq(Open, r, Close));
}
