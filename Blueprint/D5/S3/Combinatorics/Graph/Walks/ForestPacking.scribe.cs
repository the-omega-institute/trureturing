using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class ForestPackingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A family of subtrees of one finite forest has a disjoint subfamily and a vertex transversal of equal cardinality.",
        H("Packing and covering subtrees of a forest"),
        Blocks(
            Entry("forest-leaf", "exists_leaf_of_finite_forest", "A vertex with at most one neighbor", LeafFormula(),
                "Let V be a finite nonempty type in any universe u, and let G be a simple graph on V. If G is acyclic, there exists x in V whose neighbor set is subsingleton. Isolated vertices are allowed, so the neighbor set need not be nonempty. No connectedness hypothesis is imposed.",
                "Choose a simple path of greatest length. Every neighbor of its initial vertex already lies on the path, since a new neighbor would extend it. Acyclicity then identifies every such neighbor with the second vertex of the path. Thus any two neighbors are equal."),
            Entry("subtree-remove-leaf", "remove_leaf", "Removing a leaf preserves a nonsingleton subtree", RemoveFormula(),
                "Let V be any type in universe u, G a simple graph on V, A a vertex set, and x a vertex. IsSubtreeSet(G,A) means that A is nonempty and every two vertices of A are joined by an actual simple G-path whose entire vertex support lies in A. If the neighbor set of x is subsingleton and A is not the singleton containing x, then the set of vertices of A in the complement of that singleton is an IsSubtreeSet in the induced graph. In the formula, restrict(A, complement(singleton(x))) denotes the set of subtype vertices a with a.val in A. Neither finiteness nor acyclicity of G is a premise of this assertion.",
                "Nonemptiness follows because a nonempty set unequal to the singleton leaf has a vertex different from that leaf. A simple path between two such vertices cannot pass through a vertex with at most one neighbor. Its induced walk on the complement remains a simple path and all its vertices remain in A."),
            Entry("subtree-leaf-neighbor", "exists_neighbor", "A nonsingleton connected set contains a neighbor", NeighborFormula(),
                "For an arbitrary vertex type V, simple graph G and IsSubtreeSet(G,A), if x belongs to A and A is not the singleton containing x, there exists y in A adjacent to x. The graph and its vertex type may be infinite, and x need not be a leaf.",
                "Choose another vertex of A. A path inside A from x to that vertex is nonempty. Its second vertex belongs to A and is adjacent to x."),
            Entry("subtree-disjoint-lift", "disjoint_of_disjoint_remove_leaf", "Lifting disjointness across a deleted leaf", DisjointFormula(),
                "For any vertex type V and simple graph G, let A and B be IsSubtreeSet vertex sets. Suppose x has a subsingleton neighbor set, neither A nor B is the singleton containing x, and their restrictions to the complement of that singleton are disjoint. Then the original sets A and B are disjoint. No finiteness or acyclicity premise is required.",
                "A common vertex different from x contradicts disjointness of the restrictions. If x belongs to both original sets, the preceding neighbor result gives a neighbor in each set. The leaf hypothesis makes these neighbors equal, giving a common vertex different from x and the same contradiction."),
            Entry("forest-packing-cover", "forest_packing_cover", "One packing and transversal with equal size", PackingFormula(),
                "For independent universes u and v, let V be a type in Type u with Finite(V), let I be any type in Type v, let G be a simple graph on V, and let A map I to Set(V). Assume G.IsAcyclic and IsSubtreeSet(G,A(i)) for every i. There exist J : Finset(I) and X : Finset(V) such that |X| = |J|, every two distinct indices in J have disjoint original sets, and for every i in I there exists x in X belonging to A(i). The same J and X satisfy the three conclusions in the same graph and original family.",
                "Induct strongly on the number of host vertices. In a nonempty host choose a leaf x. If some family member equals the singleton containing x, select one such index and recurse on the other members that omit x in the graph with x deleted. Add the chosen index to the packing and x to the transversal; each cardinality increases by one. If no member is that singleton, delete x from every member and recurse. The removal result preserves every subtree, and the disjointness result lifts the packing to the original sets. Mapping the smaller transversal back to V preserves its size and covers every original member. In an empty host every nonempty family member is impossible, so both finite sets are empty.",
                "The index type has no finiteness or nonemptiness assumption. Empty index types, repeated vertex sets, disconnected forests and isolated vertices are included. An empty host is included whenever the hypotheses are satisfiable. A leaf, a root, an order, a packing, a transversal and a cardinality bound are all absent from the premises. The result is an unweighted existence theorem; it gives no uniqueness, algorithmic complexity, weighted-cost or infinite-host conclusion.")), []));

    private static DocumentBlock.Describe Entry(string id, string selector, string title, Formula formula, params string[] prose) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/ForestPacking." + selector),
            H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Combinatorics/jafari2026forestpacking")),
            Blocks(prose.Select(text => Paragraph(Text(text))).ToArray()), DescribeRole.Theorem);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Mem(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Host(Formula body) => All("u", Call("Universe"),
        All("V", Call("Type", F.Id("u")), All("G", Call("SimpleGraph", F.Id("V")), body)));
    private static Formula Subtree(Formula a) => Call("IsSubtreeSet", F.Id("G"), a);
    private static Formula Neighbors() => Call("neighborSet", F.Id("G"), F.Id("x"));
    private static Formula Singleton() => Call("singleton", F.Id("x"));
    private static Formula Complement() => Call("compl", Singleton());
    private static Formula Restrict(Formula a) => Call("restrict", a, Complement());

    private static Formula LeafFormula() => Disp(Host(Imp(Call("Finite", F.Id("V")),
        Imp(Call("Nonempty", F.Id("V")), Imp(Call("IsAcyclic", F.Id("G")),
            Ex("x", F.Id("V"), Call("Subsingleton", Neighbors())))))));

    private static Formula RemoveFormula()
    {
        var a = F.Id("A");
        var result = Call("IsSubtreeSet", Call("induce", F.Id("G"), Complement()), Restrict(a));
        return Disp(Host(All("A", Call("Set", F.Id("V")), Imp(Subtree(a),
            All("x", F.Id("V"), Imp(Call("Subsingleton", Neighbors()), Imp(Ne(a, Singleton()), result)))))));
    }
    private static Formula NeighborFormula()
    {
        var a = F.Id("A"); var x = F.Id("x"); var y = F.Id("y");
        var result = Ex("y", F.Id("V"), And(Mem(y, a), Call("Adj", F.Id("G"), x, y)));
        return Disp(Host(All("A", Call("Set", F.Id("V")), Imp(Subtree(a),
            All("x", F.Id("V"), Imp(Mem(x, a), Imp(Ne(a, Singleton()), result)))))));
    }
    private static Formula DisjointFormula()
    {
        var a = F.Id("A"); var b = F.Id("B");
        var result = Imp(Call("Disjoint", Restrict(a), Restrict(b)), Call("Disjoint", a, b));
        return Disp(Host(All("A", Call("Set", F.Id("V")), All("B", Call("Set", F.Id("V")),
            All("x", F.Id("V"), Imp(Subtree(a), Imp(Subtree(b),
                Imp(Call("Subsingleton", Neighbors()), Imp(Ne(a, Singleton()), Imp(Ne(b, Singleton()), result))))))))));
    }
    private static Formula PackingFormula()
    {
        var i = F.Id("i"); var j = F.Id("j"); var indices = F.Id("I");
        var selected = F.Id("J"); var x = F.Id("x"); var cover = F.Id("X");
        Formula Fiber(Formula z) => Call("A", z);
        var disjoint = All("i", indices, Imp(Mem(i, selected), All("j", indices,
            Imp(Mem(j, selected), Imp(Ne(i, j), Call("Disjoint", Fiber(i), Fiber(j)))))));
        var hits = All("i", indices, Ex("x", F.Id("V"), And(Mem(x, cover), Mem(x, Fiber(i)))));
        var result = Ex("J", Call("Finset", indices), Ex("X", Call("Finset", F.Id("V")),
            And(Eq(Call("card", cover), Call("card", selected)), disjoint, hits)));
        return Disp(Host(All("v", Call("Universe"), Imp(Call("Finite", F.Id("V")),
            All("I", Call("Type", F.Id("v")), All("A", new Formula.TypeArrow(indices, Call("Set", F.Id("V"))),
                Imp(Call("IsAcyclic", F.Id("G")), Imp(All("i", indices, Subtree(Fiber(i))), result))))))));
    }
}
