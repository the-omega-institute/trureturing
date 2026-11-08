using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ConnectivityFanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deletion connectivity produces paths to distinct terminals sharing only their source.",
        H("Terminal-clean fans"),
        Blocks(Describe.Lean(DescribeId.Create("fan"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/ConnectivityFan.exists_fan"),
            H("A fan of the full minimum size"), StatementSource.FromAuthor(MainFormula()),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
            Blocks(
                Paragraph(Text("Let V be a finite type in any universe, G a simple undirected graph on V, and k a natural number. Suppose that deleting any vertex set S of cardinality less than k leaves a connected induced graph. For every finite terminal set B and every vertex x outside B, there are exactly min(k, |B|) paths from x to distinct vertices of B. Each path meets B only at its endpoint, and two different paths share no vertex other than x.")),
                Paragraph(Text("The endpoint function e has domain Fin(min(k, |B|)); P(i) is an actual walk from x to e(i), required to be a path. Cleanliness quantifies over the full support of P(i). Pairwise intersection also uses full supports, so terminal distinctness is included explicitly. No positive lower bound on k or on |B| is assumed. If either is zero, the indexed family is empty.")),
                Paragraph(Text("Remove the edges incident with x, and take A to be the neighbors of x. Every A-to-B separator X in this graph has cardinality at least min(k, |B|): otherwise choose a terminal outside X and use connectivity after deleting X without x. A path from x to that terminal has a first neighbor in A; its remaining path avoids x and contradicts separation by X. Terminal-clean Menger certificates therefore supply min(k, |B|) mutually disjoint A-to-B paths. Prepending their edges from x gives the fan. Their original disjointness and the isolation of x ensure that the new paths share only x.")),
                Paragraph(Text("For an ordinary cycle C, taking B to be its vertex support gives a fan of size min(k, C.length), since a cycle has as many distinct vertices as edges. This cardinality does not assert that C spans the ambient vertex type or that C.length is at least k."))),
            DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("maximal-cycle-fans"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/ConnectivityFan.exists_maximal_cycle_fans"),
                H("A maximal ordinary cycle and its fans"), StatementSource.FromAuthor(CycleFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks")),
                Blocks(
                    Paragraph(Text("Assume additionally that V has at least three vertices and k is at least two. There exists an actual closed G-walk C that is a cycle, and every actual cycle in G has length at most C.length. For each vertex x outside the support, an actual fan of exactly min(k, C.length) paths has distinct endpoints on C, is terminal-clean with respect to C, and has pairwise intersection only at x. All these clauses concern the same chosen cycle C.")),
                    Paragraph(Text("A cycle exists because deletion connectivity forces every vertex to have degree at least two. An acyclic connected graph would be a tree; its edge count contradicts the sum of these degree bounds. Cycle length is bounded by the number of vertices, so a greatest attained length exists. Applying the fan theorem to that support gives the stated size and cleanliness.")),
                    Paragraph(Text("In the formula, Fan(G,x,B,r) is the existential endpoint-and-walk statement of the preceding theorem with index type Fin(r), including pathhood, terminal cleanliness, pairwise intersection only at x and injective endpoints. This theorem neither asserts that the maximal cycle spans V nor that its length is at least k."))),
                DescribeRole.Theorem)), []));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(clauses[index], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula CycleFormula()
    {
        var v = F.Id("V"); var g = F.Id("G"); var k = F.Id("k");
        var s = F.Id("S"); var c = F.Id("C"); var d = F.Id("D"); var x = F.Id("x");
        var conn = All("S", Call("Set", v), Imp(Lt(Call("ncard", s), k),
            Call("Connected", Call("induce", g, Call("compl", s)))));
        var maximal = All("b", v, All("D", Call("Walk", g, F.Id("b"), F.Id("b")),
            Imp(Call("IsCycle", d), Le(Call("length", d), Call("length", c)))));
        var fans = All("x", v, Imp(new Formula.Not(Member(x, Call("support", c))),
            Call("Fan", g, x, Call("support", c), Call("min", k, Call("length", c)))));
        var result = Ex("a", v, Ex("C", Call("Walk", g, F.Id("a"), F.Id("a")),
            And(Call("IsCycle", c), maximal, fans)));
        return Disp(All("V", Call("Type"), Imp(Call("Finite", v),
            All("G", Call("SimpleGraph", v), All("k", Call("Nat"),
                Imp(Le(Num(3), Call("card", v)), Imp(Le(Num(2), k), Imp(conn, result))))))));
    }
    private static Formula MainFormula()
    {
        var v = F.Id("V"); var g = F.Id("G"); var k = F.Id("k");
        var b = F.Id("B"); var x = F.Id("x"); var s = F.Id("S");
        var i = F.Id("i"); var j = F.Id("j"); var y = F.Id("y");
        var count = Call("min", k, Call("card", b));
        var index = Call("Fin", count);
        Formula Endpoint(Formula z) => Call("e", z);
        Formula Support(Formula z) => Call("support", Call("P", z));
        var conn = All("S", Call("Set", v), Imp(Lt(Call("ncard", s), k),
            Call("Connected", Call("induce", g, Call("compl", s)))));
        var paths = All("i", index, And(Member(Endpoint(i), b), Call("IsPath", Call("P", i)),
            All("y", v, Imp(Member(y, Support(i)), Imp(Member(y, b), Eq(y, Endpoint(i)))))));
        var intersections = All("i", index, All("j", index, Imp(Ne(i, j), All("y", v,
            Imp(Member(y, Support(i)), Imp(Member(y, Support(j)), Eq(y, x)))))));
        var conclusion = Ex("e", new Formula.TypeArrow(index, v),
            Ex("P", Call("WalkFamily", g, x, F.Id("e")),
                And(paths, intersections, Call("Injective", F.Id("e")))));
        return Disp(All("V", Call("Type"), Imp(Call("Finite", v),
            All("G", Call("SimpleGraph", v), All("k", Call("Nat"), Imp(conn,
                All("B", Call("Finset", v), All("x", v,
                    Imp(new Formula.Not(Member(x, b)), conclusion)))))))));
    }
}
