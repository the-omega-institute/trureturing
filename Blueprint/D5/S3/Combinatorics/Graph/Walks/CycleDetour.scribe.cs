using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class CycleDetourDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A path outside a cycle and an edge between its terminal successors give a longer actual cycle.",
        H("Cycle extension by a detour"),
        Blocks(Describe.Lean(DescribeId.Create("detour"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/CycleDetour.exists_cycle_through_detour"),
            H("Exact support and length of the extended cycle"),
            StatementSource.FromAuthor(MainFormula()),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
            Blocks(
                Paragraph(Text("Let G be a simple undirected graph on any type V. Let a be adjacent to s, and let p be an actual walk from s to a such that C, obtained by putting the edge a-to-s before p, is a cycle. Fix an index i strictly less than p.length. Let Q be a path from a to p.getVert(i), of length at least two, whose support meets C only at these two endpoints. Suppose s is adjacent to p.getVert(i+1). Then there is an actual cycle D based at p.getVert(i), of length C.length + Q.length - 1. Its support is exactly the union of the supports of C and Q.")),
                Paragraph(Text("No finiteness assumption on V or spanning assumption on C is needed. The index zero is permitted, as is the last index below p.length; consequently, consecutive terminal vertices and a nil residual cycle piece remain included.")),
                Paragraph(Text("Cut the detour at its first and last edges, retaining its nonempty interior path. Cut p just after its indexed terminal. Reverse the first residual cycle path, keep the second in its original direction, and place the detour interior last. The successor edge and the first and last detour edges connect these three pieces into a ring. The old cycle vertices occur exactly once, and every interior detour vertex occurs exactly once outside that cycle.")),
                Paragraph(Text("Induce each piece on the subtype defined by the union of these actual supports. Their support lists partition every vertex of that subtype with count one, and the list has length at least three. The path-ring splicing theorem gives a Hamiltonian cycle on this subtype. Mapping by the injective inclusion gives D in G; the support inventory yields its exact union and its length. Hamiltonicity here concerns the union subtype only."))),
            DescribeRole.Theorem)), []));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(clauses[index], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula MainFormula()
    {
        var v = F.Id("V"); var g = F.Id("G"); var a = F.Id("a"); var s = F.Id("s");
        var p = F.Id("p"); var q = F.Id("Q"); var i = F.Id("i"); var d = F.Id("D");
        var c = Call("cons", Call("edge", a, s), p);
        var terminal = Call("getVert", p, i);
        var assumptions = And(Call("Adj", g, a, s), Call("IsCycle", c),
            Rel(i, FormulaRelationOperator.LessThan, Call("length", p)), Call("IsPath", q),
            Rel(Num(2), FormulaRelationOperator.LessThanOrEqual, Call("length", q)),
            Call("TerminalClean", q, c, a, terminal),
            Call("Adj", g, s, Call("getVert", p, Add(i, Num(1)))));
        var result = Ex("D", Call("Walk", g, terminal, terminal), And(Call("IsCycle", d),
            Equal(Call("length", d), Subtract(Add(Call("length", c), Call("length", q)), Num(1))),
            Equal(Call("supportSet", d), Call("union", Call("supportSet", c), Call("supportSet", q)))));
        return Disp(All("V", Call("Type"), All("G", Call("SimpleGraph", v),
            All("a", v, All("s", v, All("p", Call("Walk", g, s, a),
                All("i", Call("Nat"), All("Q", Call("Walk", g, a, terminal), Imp(assumptions, result)))))))));
    }
}
