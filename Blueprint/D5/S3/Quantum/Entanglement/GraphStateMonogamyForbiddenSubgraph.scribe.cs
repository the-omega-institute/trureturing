using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class GraphStateMonogamyForbiddenSubgraphDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/GraphStateMonogamyForbiddenSubgraph.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/fuentes2025mmigraphstates");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every graph state that violates monogamy of mutual information is carried by local complementations to a graph with an induced four-star, and that graph is a generalized star for the partition that places the three leaves of the star in their own parts and every other vertex in the centre. This proves the forbidden-subgraph conjecture of Fuentes, Keeler, Munizzi and Pollack for every number of qubits.",
        H("The forbidden-subgraph conjecture for MMI in graph states"),
        Blocks(
            Node("lc", "Local complementation", LcFormula(),
                "Local complementation at v complements the adjacency between any two neighbours of v and keeps every other adjacency; on graph states it realizes the local Clifford operations.",
                "lc", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lcseq", "LC equivalence", LcSeqFormula(),
                "lcSeq(G, s) applies local complementation at the vertices of the list s, first to last; H is LC-equivalent to G when H = lcSeq(G, s) for some list s.",
                "lcSeq", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claw", "Induced four-star", ClawFormula(),
                "The vertex c is adjacent to three distinct vertices i, j, k that are pairwise non-adjacent, so c, i, j, k induce the four-vertex star that the paper denotes K_4.",
                "IsClaw", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("entropy", "Entanglement entropy of a graph state", EntropyFormula(),
                "The entropy of a set A of qubits in the graph state of G is the rank of the adjacency block of A: every matrix M over Z_2 with rows indexed by A and columns by the complement of A whose entry at x, y is 1 when x and y are adjacent and 0 otherwise has rank S(G, A).",
                "entropy", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mmi", "Violation of MMI", ViolatesFormula(),
                "The graph state violates an instance of monogamy of mutual information: pairwise disjoint sets I, J, K with S(I ∪ J) + S(I ∪ K) + S(J ∪ K) less than S(I) + S(J) + S(K) + S(I ∪ J ∪ K).",
                "ViolatesMMI", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("star", "Generalized star", StarFormula(),
                "H is a generalized star with centre C and parts P_1, ..., P_k: the parts are nonempty and pairwise disjoint, the centre is disjoint from every part, the centre and the parts cover all vertices (univ), no edge joins two different parts, and every part has a vertex adjacent to a vertex of the centre.",
                "IsGeneralizedStar", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The forbidden-subgraph conjecture", ClaimFormula(),
                "For every number n of qubits and every graph G on the vertices 0, ..., n - 1 whose graph state violates MMI, some graph H = lcSeq(G, s) has an induced four-star c; i, j, k, and H is a generalized star with centre univ \\ {i, j, k}, the vertices other than i, j, k, and parts {i}, {j}, {k}.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Proof of the conjecture", Disp(F.Id("claim")),
                "Local complementation at a vertex of a vertex set commutes with restriction to that set, so an induced four-star or a relabelled graph reached on part of the vertices lifts to the whole graph. A connected graph has an ordering of its vertices in which each vertex after the first is adjacent to an earlier one; the graph on the first m + 1 vertices is that on the first m with a new vertex adjacent to a nonempty set T, which local complementation at earlier vertices keeps nonempty. For the representatives K_1, K_2, the path on three vertices, the path 1 - 2 - 3 - 0, the 5-cycle 0 - 1 - 3 - 4 - 2 - 0 and the triangular prism with triangles 012, 345 and matching 03, 14, 25, and every nonempty T, a listed sequence of at most three local complementations carries the extension to a graph with an induced four-star or to a relabelling of the next representative, and every extension of the prism reaches an induced four-star; these 120 certificates are checked by evaluation. So a connected graph reaching no induced four-star has at most six vertices and is carried to a relabelled representative. Local complementation at v changes the adjacency block of A by the row operation 1 + u e_v^T (u_v = 0) when v is in A, an involution over Z_2, and the entropy of A equals that of its complement, so no entropy changes; relabelling permutes rows and columns. A vertex set without edges to its complement makes every adjacency block block-diagonal, so entropies add over components. The representatives satisfy MMI: for K_1, K_2, the 3-path, the 5-cycle and the prism a parity criterion makes the rows of every set of at most half the vertices independent, so the entropy of A is min(|A|, n - |A|) and MMI reduces to arithmetic; for the 4-path a violation needs four nonempty parts, hence single vertices, and the three pairs have entropies at least 2, 2 and 1. By induction on the number of vertices, a graph state reaching no induced four-star therefore satisfies MMI. Conversely, given an induced four-star c; i, j, k, the leaves are pairwise non-adjacent and adjacent to c, which lies in the centre, so the partition is a generalized star.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fuentes-2025-mmi-forbidden-subgraph"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("mmistar-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Not(Formula value) => new Formula.Not(Parenthesized(value));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Ex(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Adj(Formula graph, Formula a, Formula b) => Call("Adj", graph, a, b);
    private static Formula Union(Formula left, Formula right) => Call("union", left, right);
    private static Formula S(Formula graph, Formula set) => Call("entropy", graph, set);
    private static Formula Singleton(Formula x) => Seq(OpenBrace, x, CloseBrace);

    private static Formula LcFormula()
    {
        Formula g = F.Id("G"), v = F.Id("v"), a = F.Id("a"), b = F.Id("b");
        return Disp(Iff(Adj(Call("lc", g, v), a, b),
            And(NotEqual(a, b), Parenthesized(Iff(Adj(g, a, b), Not(And(Adj(g, v, a), Adj(g, v, b))))))));
    }

    private static Formula LcSeqFormula()
    {
        Formula g = F.Id("G"), v = F.Id("v"), s = F.Id("s");
        return Disp(And(
            Parenthesized(Equal(Call("lcSeq", g, Named("nil")), g)),
            Parenthesized(Equal(Call("lcSeq", g, Call("cons", v, s)), Call("lcSeq", Call("lc", g, v), s)))));
    }

    private static Formula ClawFormula()
    {
        Formula g = F.Id("G"), c = F.Id("c"), i = F.Id("i"), j = F.Id("j"), k = F.Id("k");
        Formula body = And(Adj(g, c, i), And(Adj(g, c, j), And(Adj(g, c, k),
            And(NotEqual(i, j), And(NotEqual(i, k), And(NotEqual(j, k),
                And(Not(Adj(g, i, j)), And(Not(Adj(g, i, k)), Not(Adj(g, j, k))))))))));
        return Disp(Iff(Call("IsClaw", g, c, i, j, k), body));
    }

    private static Formula EntropyFormula()
    {
        Formula g = F.Id("G"), a = F.Id("A"), m = F.Id("M"), x = F.Id("x"), y = F.Id("y");
        Formula outside = Call("compl", a);
        Formula entry = Equal(new Formula.Apply(m, [x, y]),
            Seq(Named("if"), Sp, Adj(g, x, y), Sp, Named("then"), Sp, D(1), Sp, Named("else"), Sp, D(0)));
        Formula blocks = Call("Matrix", a, outside, Call("ZMod", D(2)));
        return Disp(All("M", blocks, Implies(Parenthesized(All("x", a, All("y", outside, entry))),
            Equal(S(g, a), Call("rank", m)))));
    }

    private static Formula ViolatesFormula()
    {
        Formula g = F.Id("G"), i = F.Id("I"), j = F.Id("J"), k = F.Id("K");
        Formula disjoint = And(Call("Disjoint", i, j), And(Call("Disjoint", i, k), Call("Disjoint", j, k)));
        Formula lhs = Add(Add(S(g, Union(i, j)), S(g, Union(i, k))), S(g, Union(j, k)));
        Formula rhs = Add(Add(Add(S(g, i), S(g, j)), S(g, k)), S(g, Union(Union(i, j), k)));
        Formula sets = Call("Finset", F.Id("V"));
        return Disp(Iff(Call("ViolatesMMI", g),
            Ex("I", sets, Ex("J", sets, Ex("K", sets, And(disjoint, Less(lhs, rhs)))))));
    }

    private static Formula StarFormula()
    {
        Formula h = F.Id("H"), c = F.Id("C"), p = F.Id("p"), q = F.Id("q"), x = F.Id("x"), y = F.Id("y"), z = F.Id("z");
        Formula part = Call("P", p), partQ = Call("P", q);
        Formula parts = Call("Fin", F.Id("k"));
        Formula nonempty = All("p", parts, Call("Nonempty", part));
        Formula disjointParts = All("p", parts, All("q", parts, Implies(NotEqual(p, q), Call("Disjoint", part, partQ))));
        Formula disjointCentre = All("p", parts, Call("Disjoint", c, part));
        Formula cover = Equal(Union(c, Call("biUnion", Named("univ"), F.Id("P"))), Named("univ"));
        Formula noEdge = All("p", parts, All("q", parts, Implies(NotEqual(p, q),
            Parenthesized(All("x", part, All("y", partQ, Not(Adj(h, x, y))))))));
        Formula anchored = All("p", parts, Ex("x", part, Ex("z", c, Adj(h, x, z))));
        return Disp(Iff(Call("IsGeneralizedStar", h, c, F.Id("P")),
            And(nonempty, And(disjointParts, And(disjointCentre, And(cover, And(noEdge, anchored)))))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), g = F.Id("G"), s = F.Id("s"), c = F.Id("c"), i = F.Id("i"), j = F.Id("j"), k = F.Id("k");
        Formula vertices = Call("Fin", n);
        Formula h = Call("lcSeq", g, s);
        Formula centre = Call("sdiff", Named("univ"), Seq(OpenBrace, i, Comma, j, Comma, k, CloseBrace));
        Formula partsList = Seq(Open, Singleton(i), Comma, Singleton(j), Comma, Singleton(k), Close);
        Formula body = Ex("s", Call("List", vertices), Ex("c", vertices, Ex("i", vertices, Ex("j", vertices,
            Ex("k", vertices, And(Call("IsClaw", h, c, i, j, k), Call("IsGeneralizedStar", h, centre, partsList)))))));
        return Disp(Iff(F.Id("claim"), All("n", Naturals(), All("G", Call("SimpleGraph", vertices),
            Implies(Call("ViolatesMMI", g), body)))));
    }
}
