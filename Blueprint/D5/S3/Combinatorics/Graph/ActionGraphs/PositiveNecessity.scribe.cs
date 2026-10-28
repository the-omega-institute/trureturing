using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ActionGraphs;

internal sealed class PositiveNecessityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ActionGraphs/PositiveNecessity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/klanderman2026generalizedactiongraphs");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The constant sequence one admits generalized action graphs at every stage: the directed paths from zero to n. Its convolution coefficients cannot all be strictly positive.",
        H("Directed paths and strictly positive convolution necessity"),
        Blocks(
            Node("graphs", "The three generalized action-graph axioms", GraphFormula(),
                "IsGeneralizedActionGraph", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                "Definition 1.1: “The sequence Gn of generalized action graphs for a particular sequence sn of positive integers is a sequence of directed, labeled, rooted trees such that: Axiom 1 Define G0 as the graph with s0 vertices labeled 0 and no edges. Construct Gn from Gn−1 by adding sn new vertices, which are each labeled n. Axiom 2 For vertex v in Gn, the subtree of Gn with root v is isomorphic to some Gk such that k ≤ n. Axiom 3 All leaves in the graph Gn have label n.” Finite vertex types V(n), native directed graphs G(n), roots, labels and injective maps step(n) retain the actual graphs. The underlying simple graph is a tree, every vertex is reachable from the root, and there is no nonempty directed closed walk. The maps retain the old root, labels and edges; their complements have exactly s(n+1) vertices, all labeled n+1. The subtype in Axiom 2 consists of every descendant, including its root, with exactly the edges inherited from G(n). RelIso preserves and reflects directed adjacency. Its root equation and a single additive shift describe the rooted labeled isomorphism. Section 3.1 states: “Note that when we consider isomorphism in generalized action graphs, the labels on the vertices may be shifted, but the underlying structure of the graphs are the same.” A leaf is a vertex with no outgoing edge."),
            Node("claim", "The strictly positive necessity question", Disp(Equal(Named("claim"), ClaimBody())),
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                "Section 4 asks: “Another open question is whether the hypotheses of Theorem 1.1 are in fact necessary conditions for generalized action graphs to exist.” The displayed proposition quantifies every positive integer sequence and the existence of an entire family satisfying Definition 1.1. The conclusion includes s(0)=1 and a strictly positive coefficient z(i) for every i at least one. The unused value z(0) has no restriction and occurs in no sum. All graph stages and all convolution equations are quantified."),
            Node("result", "Refutation by the entire directed-path family", Disp(new Formula.Not(Par(ClaimBody()))),
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                "Set s(n)=1 for every natural n. At stage n take Fin(n+1), root zero, labels equal to vertex values and the directed covering relation: an edge goes from i to i+1. Forgetting orientation gives Mathlib's pathGraph(n+1), which is a tree. Reachability is the order relation, and nonempty directed reachability is strict order, so directed cycles do not occur. Fin.castSuccEmb retains the previous graph and adds just its new last vertex. For any vertex i, translation j ↦ i+j is a bijection from Fin(n−i+1) to its actual descendant subtype, preserving directed edges and its root and shifting every label by i. The only leaf is n. These statements include n=0 and i=n. If strictly positive z satisfied the convolution, the equations at one and two would give z(1)=1 and 1=z(1)+z(2), forcing z(2)=0. The strictly positive necessity proposition is therefore false. No conclusion about the nonnegative-coefficient variant follows.")),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula,
        string declaration, DescribeRole role, AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("kmt-positive-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Times(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula All(string v, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), type, body);
    private static Formula Some(string v, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), type, body);
    private static Formula LambdaOf(string v, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Par(Seq(F.Id(v), Colon, type)), Sp, Mapsto, Sp, body);
    private static Formula First(Formula a) => Seq(Par(a), Dot, D(1));
    private static Formula Adj(Formula n) => Seq(Par(Call("G", n)), Dot, Named("Adj"));
    private static Formula Edge(Formula n, Formula a, Formula b) => new Formula.Apply(Adj(n), [a, b]);
    private static Formula Reach(Formula n, Formula a, Formula b) =>
        QCall("Relation", "ReflTransGen", Adj(n), a, b);
    private static Formula Descendants(Formula n, Formula v) =>
        Seq(OpenBrace, F.Id("w"), Colon, Call("V", n), Sp, Slash, Slash, Sp,
            Reach(n, v, F.Id("w")), CloseBrace);
    private static Formula NewVertices(Formula n) =>
        Seq(OpenBrace, F.Id("v"), Colon, Call("V", Add(n, D(1))), Sp, Slash, Slash, Sp,
            NotOld(n, F.Id("v")), CloseBrace);
    private static Formula NotOld(Formula n, Formula v) =>
        new Formula.Not(Seq(v, Sp, InMacro, Sp, QCall("Set", "range", Call("step", n))));
    private static Formula Embedding(Formula n) =>
        QCall("Function", "Embedding", Call("V", n), Call("V", Add(n, D(1))));

    private static Formula GraphArguments(FormulaQuantifier quantifier, Formula body)
    {
        Formula Bind(string v, Formula type, Formula rest) =>
            new Formula.Bind(quantifier, FormulaIdentifier.Create(v), type, rest);
        Formula n = F.Id("n");
        return Bind("V", Arrow(Naturals(), Named("Type")),
            Bind("G", All("n", Naturals(), Call("Digraph", Call("V", n))),
            Bind("root", All("n", Naturals(), Call("V", n)),
            Bind("label", All("n", Naturals(), Arrow(Call("V", n), Naturals())),
            Bind("step", All("n", Naturals(), Embedding(n)), body)))));
    }

    private static Formula GraphFormula()
    {
        Formula n = F.Id("n"), v = F.Id("v"), w = F.Id("w"), k = F.Id("k");
        Formula trees = All("n", Naturals(),
            And(Call("Finite", Call("V", n)),
            And(Seq(Par(Seq(Par(Call("G", n)), Dot, Named("toSimpleGraphInclusive"))), Dot, Named("IsTree")),
            And(All("v", Call("V", n), Reach(n, Call("root", n), v)),
                All("v", Call("V", n), new Formula.Not(QCall("Relation", "TransGen", Adj(n), v, v)))))));
        Formula initial = And(Equal(QCall("Nat", "card", Call("V", D(0))), Call("s", D(0))),
            And(All("v", Call("V", D(0)), Equal(Call("label", D(0), v), D(0))),
                All("v", Call("V", D(0)), All("w", Call("V", D(0)), new Formula.Not(Edge(D(0), v, w))))));
        Formula next = Add(n, D(1));
        Formula stepV = Call("step", n, v), stepW = Call("step", n, w);
        Formula growth = All("n", Naturals(),
            And(Equal(Call("step", n, Call("root", n)), Call("root", next)),
            And(All("v", Call("V", n), Equal(Call("label", next, stepV), Call("label", n, v))),
            And(All("v", Call("V", n), All("w", Call("V", n), Iff(Edge(next, stepV, stepW), Edge(n, v, w)))),
            And(Equal(QCall("Nat", "card", NewVertices(n)), Call("s", next)),
                All("v", Call("V", next), Implies(NotOld(n, v), Equal(Call("label", next, v), next))))))));
        Formula descendantType = Descendants(n, v);
        Formula restricted = LambdaOf("a", descendantType,
            LambdaOf("b", descendantType, Edge(n, First(F.Id("a")), First(F.Id("b")))));
        Formula subtrees = All("n", Naturals(), All("v", Call("V", n),
            Some("k", Naturals(), And(Leq(k, n),
                Some("e", Call("RelIso", Adj(k), restricted),
                    And(Equal(Call("e", Call("root", k)),
                        Seq(Langle, v, Comma, Seq(Qualified("Relation", "ReflTransGen"), Dot, Named("refl")), Rangle)),
                        Some("shift", Naturals(), All("w", Call("V", k),
                            Equal(Call("label", n, First(Call("e", w))), Add(Call("label", k, w), F.Id("shift"))))))))));
        Formula leaves = All("n", Naturals(), All("v", Call("V", n),
            Implies(All("w", Call("V", n), new Formula.Not(Edge(n, v, w))), Equal(Call("label", n, v), n))));
        Formula body = And(trees, And(And(initial, growth), And(subtrees, leaves)));
        return Disp(All("s", Arrow(Naturals(), Naturals()), GraphArguments(FormulaQuantifier.ForAll,
            Equal(Call("IsGeneralizedActionGraph", F.Id("s"), F.Id("V"), F.Id("G"), F.Id("root"),
                F.Id("label"), F.Id("step")), body))));
    }

    private static Formula ClaimBody()
    {
        Formula s = F.Id("s"), n = F.Id("n"), i = F.Id("i");
        Formula existence = GraphArguments(FormulaQuantifier.Exists,
            Call("IsGeneralizedActionGraph", s, F.Id("V"), F.Id("G"), F.Id("root"), F.Id("label"), F.Id("step")));
        Formula sum = Seq(new Formula.Subscript(F.Sum,
                Seq(i, Sp, InMacro, Sp, QCall("Finset", "Icc", D(1), n))), Sp,
            Par(Times(Call("z", i), Call("s", Subtract(n, i)))));
        Formula coefficients = Some("z", Arrow(Naturals(), Naturals()),
            And(All("i", Naturals(), Implies(Leq(D(1), i), Less(D(0), Call("z", i)))),
                All("n", Naturals(), Implies(Leq(D(1), n), Equal(Call("s", n), sum)))));
        return All("s", Arrow(Naturals(), Naturals()),
            Implies(All("n", Naturals(), Less(D(0), Call("s", n))),
                Implies(existence, And(Equal(Call("s", D(0)), D(1)), coefficients))));
    }
}
