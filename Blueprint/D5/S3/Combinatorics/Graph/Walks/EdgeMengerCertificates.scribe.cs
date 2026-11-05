using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class EdgeMengerCertificatesDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/traversogianini2026brooks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite edge-deletion resilience is equivalent to pairwise edge-disjoint path certificates.",
        H("Finite edge-Menger certificates"),
        Blocks(Describe.Lean(DescribeId.Create("edge-reachability-iff"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/EdgeMengerCertificates.isEdgeReachable_iff"),
            H("Deletion resilience and edge-disjoint paths"),
            StatementSource.FromAuthor(MainFormula()), AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("For every vertex type V in any universe with Finite(V), every simple undirected graph G on V, every natural number k, and all vertices u and v, the native G.IsEdgeReachable(k,u,v) is equivalent to a family p indexed by Fin(k) of G-walks from u to v, each satisfying IsPath, whose edge lists are pairwise List.Disjoint at distinct indices.")),
                Paragraph(Text("The left side is displayed with the native definition expanded: for every S : Set(Sym2(V)), if encard(S) is strictly less than the natural k coerced to ENat, u and v are reachable in G.deleteEdges(S). S ranges over all sets of unordered vertex pairs, including pairs that are not graph edges. The theorem concerns natural k, not arbitrary infinite ENat thresholds. WalkFamily(G,u,v,k) in the formula means the function type Fin(k) to G.Walk(u,v). ListDisjoint is List.Disjoint of the two complete unordered edge lists.")),
                Paragraph(Text("The scope includes k=0, u=v, an empty vertex type, edge-free graphs, adjacent endpoints and zero-length paths. For u=v the certificate is the constant family of nil paths for every k; distinct indices need not denote distinct walks. Edge-disjoint paths may share internal vertices. No connectedness, nonempty-graph, endpoint-nonadjacency or positive-length assumption is imposed. Directed, infinite-vertex and vertex-disjoint variants are outside this statement.")),
                Paragraph(Text("For distinct endpoints, apply the first conjunct of the public MengerCertificates.exists_separator_paths_and_weak_duality directly to G.lineGraph. Its vertices are actual edges of G, and its terminal sets consist of the edges incident to u and v; these sets may overlap. Project a line-graph separator to an edge-deletion set. A surviving deleted-graph walk lifts to a line-graph walk with controlled support, contradicting separation unless k is at most the separator size. Lower the resulting vertex-disjoint line walks to original walks, then bypass them to paths while preserving edge containment and hence edge disjointness. Restrict indices with Fin.castLE. A nil line walk can lower to a single original edge for distinct adjacent endpoints. The reverse direction chooses a deleted edge met by each walk; disjointness makes this choice injective and contradicts encard(S)<k.")),
                Paragraph(Text("The received proof source is Juan Pablo Traverso Gianini's jtraverso/menger-hamiltonian, immutable commit 35c5f684f9bfbd244bd0999ce725623ab571adb6: MengerCore.lean's lift_to_lineGraph, walk_in_edge and lower_from_lineGraph, and Menger.lean's isEdgeReachable_iff. The source attributes Menger's theorem to Diestel, Graph Theory, Theorem 3.3.1, second proof (Boehme, Goering, Harant). The receiver uses its frozen public vertex certificate instead of duplicating that proof. This is known mathematics with credited source reception; no originality or reading of the original Diestel text is claimed.")),
                Paragraph(Text("The source copyright and complete Apache license are retained in the Lean source and docs/reports/licenses/menger-hamiltonian-LICENSE.txt. Retire this port only when this repository's own adopted Mathlib pin supplies the equivalent full finite edge theorem and affected consumers and records migrate lawfully."))),
            DescribeRole.Theorem)),
        []));

    private static Formula MainFormula()
    {
        var vType = F.Id("V"); var graph = F.Id("G"); var k = F.Id("k");
        var u = F.Id("u"); var v = F.Id("v"); var s = F.Id("S");
        var p = F.Id("p"); var i = F.Id("i"); var j = F.Id("j");
        var fin = Call("Fin", k);
        var resilient = All("S", Call("Set", Call("Sym2", vType)),
            Imp(Lt(Call("encard", s), Call("NatToENat", k)),
                Call("Reachable", Call("deleteEdges", graph, s), u, v)));
        var paths = Ex("p", Call("WalkFamily", graph, u, v, k),
            And(All("i", fin, Call("IsPath", Call("p", i))),
                All("i", fin, All("j", fin, Imp(Ne(i, j),
                    Call("ListDisjoint", Call("edges", Call("p", i)),
                        Call("edges", Call("p", j))))))));
        return Disp(All("V", Call("Type"), Imp(Call("Finite", vType),
            All("G", Call("SimpleGraph", vType), All("k", Call("Nat"),
                All("u", vType, All("v", vType, Iff(resilient, paths))))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0
            ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
}
