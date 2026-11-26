using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class TripleHellyRecognitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Triple intersections of connected induced vertex sets characterize connected acyclic graphs on arbitrary vertex types.",
        H("Trees and triple Helly intersections"),
        Blocks(
            Describe.Lean(DescribeId.Create("cycle-obstruction"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/TripleHellyRecognition.exists_connected_triple_obstruction"),
                H("Three connected sets from any cycle"),
                StatementSource.FromAuthor(ObstructionFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let u be any universe, V a type in Type u, G a simple undirected graph on V, v a vertex, and p a native G.Walk from v to v. If p.IsCycle, there exist vertex sets A, B and C such that all three induced graphs are connected, each of A intersect B, B intersect C and C intersect A is nonempty, and A intersect B intersect C is empty. Neither G nor its vertex type is required to be finite or connected.")),
                    Paragraph(Text("Write the first two edges of the cycle as x-to-y and y-to-z, and let r be the remaining walk from z to x. A cycle has at least three edges. Set A equal to the pair containing x and y, B equal to the pair containing y and z, and C equal to the support of r. Adjacency makes the induced graphs on A and B connected, while the induced graph on the support of any walk is connected. This last fact does not require the walk to be a path.")),
                    Paragraph(Text("The vertices y, z and x belong respectively to A intersect B, B intersect C and C intersect A. The cycle condition makes the support after its first vertex duplicate-free, so y does not belong to the support of r. Also x differs from z: equality would repeat the first edge in the opposite direction, contradicting the cycle's edge distinctness. Thus the only possible common vertex of A and B is y, and it is absent from C. This proves the empty triple intersection.")),
                    Paragraph(Text("All three induced graphs use the edges of the original ambient graph. Chords and other extra ambient edges are permitted; they cannot destroy the exhibited connections or change the memberships of the three vertex sets. In a triangle the remaining walk is a single edge, and the same construction applies."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tree-recognition"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/TripleHellyRecognition.isTree_iff_connected_triple_helly"),
                H("Recognition among connected graphs"),
                StatementSource.FromAuthor(RecognitionFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every universe u, every V in Type u, every simple graph G on V and every proof of G.Connected, G.IsTree is equivalent to the following property. For all sets A, B and C of vertices, if each induced graph is connected and each of the three pair intersections is nonempty, then A intersect B intersect C is nonempty. The quantifiers allow repeated sets and an infinite ambient vertex type. Native Connected includes nonemptiness, and native IsTree consists of connectedness together with the absence of native cyclic walks.")),
                    Paragraph(Text("For the forward implication, apply the finite-family subtree Helly theorem to the family indexed by Fin(3), with values A, B and C. The three off-diagonal intersections are given, their reverse orders follow by commutativity, and the diagonal intersections are nonempty because the sets already have pairwise intersections. Only this indexing family is finite. The ambient vertex type remains arbitrary.")),
                    Paragraph(Text("For the reverse implication, take any actual closed walk and suppose it is a cycle. The preceding construction supplies A, B and C satisfying every premise of the triple property but having empty triple intersection. The asserted nonempty triple intersection is a contradiction. Hence every closed walk fails to be a cycle, which is exactly native IsAcyclic. Together with the assumed connectedness this yields native IsTree.")),
                    Paragraph(Text("The forward implication uses SimpleGraph.IsTree.inter_nonempty_of_pairwise from SubtreeHelly, whose proof source and Apache attribution are recorded there and in its Library note. The cycle construction and the converse are derived here from native walk facts. No claim about literature priority is made. The characterization concerns three sets; it asserts neither an infinite-family intersection property nor an algorithmic bound."))),
                DescribeRole.Theorem)), []));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Inter(Formula left, Formula right) => Call("inter", left, right);
    private static Formula Conn(Formula graph, Formula set) => Call("Connected", Call("induce", graph, set));
    private static Formula Nonempty(Formula set) => Call("Nonempty", set);
    private static Formula ForGraphs(Formula statement) =>
        Disp(All("u", Call("Universe"), All("V", Call("Type", F.Id("u")),
            All("G", Call("SimpleGraph", F.Id("V")), statement))));
    private static Formula ObstructionFormula()
    {
        var v = F.Id("V"); var g = F.Id("G"); var a = F.Id("A");
        var b = F.Id("B"); var c = F.Id("C"); var x = F.Id("v"); var p = F.Id("p");
        var conclusion = And(Conn(g, a), Conn(g, b), Conn(g, c),
            Nonempty(Inter(a, b)), Nonempty(Inter(b, c)), Nonempty(Inter(c, a)),
            Equal(Inter(Inter(a, b), c), Call("emptyset", v)));
        var sets = Call("Set", v);
        var existence = Ex("A", sets, Ex("B", sets, Ex("C", sets, conclusion)));
        var overWalks = All("v", v, All("p", Call("Walk", g, x, x),
            Imp(Call("IsCycle", p), existence)));
        return ForGraphs(overWalks);
    }
    private static Formula RecognitionFormula()
    {
        var v = F.Id("V"); var g = F.Id("G"); var a = F.Id("A");
        var b = F.Id("B"); var c = F.Id("C"); var sets = Call("Set", v);
        var assumptions = And(Conn(g, a), Conn(g, b), Conn(g, c),
            Nonempty(Inter(a, b)), Nonempty(Inter(b, c)), Nonempty(Inter(c, a)));
        var property = All("A", sets, All("B", sets, All("C", sets,
            Imp(assumptions, Nonempty(Inter(Inter(a, b), c))))));
        var equivalence = new Formula.Logic(Call("IsTree", g), FormulaLogicOperator.Iff, property);
        return ForGraphs(Imp(Call("Connected", g), equivalence));
    }
}
