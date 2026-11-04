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
            DescribeRole.Theorem)), []));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.ForAll(name, type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Exists(name, type, body);
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
