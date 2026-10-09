using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SeidelSwitching;

internal sealed class VertexIdentitySwitchesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SeidelSwitching/VertexIdentitySwitches.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/gervacio2026identityseidel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite nonempty simple graph has every vertex as an identity Seidel switch if and only if it has one vertex. Edge-count preservation forces regularity, and switching at a vertex changes the degree of each other vertex by one.",
        H("Every vertex an identity Seidel switch"),
        Blocks(
            Node("switch", "Seidel switching across a subset", "seidelSwitch", SwitchFormula(),
                "Theorem 2.6, page 6: \"Let G be a graph and S a non-empty subset of V(G). Then S(G) is obtained from G by deleting all edges xy with x ∈ S and y ∈ V(G) ∖ S, and adding all non-edges xy with x ∈ S and y ∈ V(G) ∖ S. Edges with both ends in S or both ends in V(G) ∖ S remain unchanged.\" The displayed adjacency relation is the subset switch: different membership in S negates G.Adj, equal membership preserves it, and x ≠ y excludes loops. For the empty subset the relation is G.Adj, agreeing with the source's empty-switch convention on page 6. Section 2.1, page 3: \"Let G be a graph and v ∈ V(G). The Seidel switch of G by v, denoted v(G), is the graph obtained from G by deleting all edges vy where y ∈ N_G(v) and adding all edges vz where z ∈ V(G) ∖ N_G(v) and z ≠ v. In other words, we complement the adjacency relation between v and the rest of the vertex set, while leaving all other adjacencies unchanged.\" Taking S = {v} gives this vertex switch.",
                AssessedProvenance.FromLiterature(Source)),
            Node("vertex", "Vertex identity Seidel switch", "IsVertexISS", VertexFormula(),
                "Definition 4.1, page 8: \"Let G be a graph. A subset S ⊆ V(G) is called an identity Seidel switch (abbreviated ISS) if S(G) ≅ G.\" Section 4, page 9: \"We say that {x} is a vertex-ISS if {x} is an ISS, and that {x, y} is an edge-ISS if {x, y} is an ISS and xy ∈ E(G).\" Nonempty expresses existence of a graph isomorphism; the cut is precisely the singleton {x}.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The complete characterization", "claim", ClaimFormula(),
                "Problem 6.1, page 13: \"Characterize graphs G for which every vertex is a vertex-ISS. Lemma 4.4 gives a necessary condition in terms of the minimum and maximum degree; can this be strengthened to a complete characterization?\" Section 2, page 3: \"Throughout, a graph G is an ordered pair G = ⟨V(G), E(G)⟩ where V(G) is a non-empty finite set whose elements are called vertices and E(G) is a set of 2-element subsets of V(G) called edges.\" V is any Type with Fintype, DecidableEq and Nonempty instances, and G is any SimpleGraph on V. The answer is that its cardinality equals one. There is no connectivity, regularity, or adjacency-decidability hypothesis.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(DescribeId.Create("seidel-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Exactly the one-vertex graph"), StatementSource.FromAuthor(Disp(Call("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Switching at v leaves the nonincident edges unchanged. The old and new incident-edge counts are the two complementary neighbour counts, whose sum is card(V)−1. Hence the new edge count plus twice degree(v) equals the old edge count plus card(V)−1. An identity switch preserves the edge count; if every vertex is an identity switch, twice every degree equals card(V)−1. If card(V)>1 this forces a positive common degree. Choose a neighbour w of v. Switching at v lowers the degree of w by one, while the isomorphism would send w to a vertex with the original common degree: contradiction. At order one the adjacency relation is empty and the switch equals G. More generally, at a vertex y, switching across S preserves same-side neighbours and exchanges crossing neighbours with crossing non-neighbours. The new degree plus twice the old crossing-neighbour count equals the old degree plus the number of vertices on the opposite side. This identity includes empty and full cuts. Natural subtraction denotes truncated subtraction. The literal conclusion of Lemma 4.4 includes a same-vertex case in the one-vertex graph; an adjacency assertion there needs distinct vertices. The characterization does not answer Problems 6.2–6.4."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("gervacio-2026-vertex-identity-seidel-switches"),
                    ResolutionKind.Proved))), []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("seidel-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Qualified(string name)
    {
        var parts = name.Split('.');
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (tokens.Count != 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq([.. tokens]);
    }
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(Qualified(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(Qualified(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Instances(Formula body, params Formula[] types)
    {
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (var type in types) tokens.Add(Seq(OpenBracket, type, CloseBracket, Sp));
        tokens.Add(body);
        return Seq([.. tokens]);
    }
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Member(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Singleton(Formula x) => Seq(OpenBrace, x, CloseBrace);
    private static Formula V() => F.Id("V");
    private static Formula G() => F.Id("G");
    private static Formula Graph() => Call("SimpleGraph", V());
    private static Formula GraphBinders(Formula body) => All("V", F.Id("Type"), All("G", Graph(), body));
    private static Formula SwitchFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), s = F.Id("S");
        Formula adjacency = And(Rel(x, FormulaRelationOperator.NotEqual, y),
            Iff(Call("SimpleGraph.Adj", G(), x, y), Iff(Member(x, s), Member(y, s))));
        return GraphBinders(All("S", Call("Set", V()), All("x", V(), All("y", V(),
            Iff(Call("SimpleGraph.Adj", Call("seidelSwitch", G(), s), x, y), adjacency)))));
    }
    private static Formula VertexFormula()
    {
        Formula x = F.Id("x");
        Formula iso = Call("SimpleGraph.Iso", Call("seidelSwitch", G(), Singleton(x)), G());
        return GraphBinders(All("x", V(), Iff(Call("IsVertexISS", G(), x), Call("Nonempty", iso))));
    }
    private static Formula ClaimFormula()
    {
        Formula body = Iff(All("x", V(), Call("IsVertexISS", G(), F.Id("x"))),
            Equal(Call("Fintype.card", V()), D(1)));
        Formula quantified = All("V", F.Id("Type"), Instances(All("G", Graph(), body),
            Call("Fintype", V()), Call("DecidableEq", V()), Call("Nonempty", V())));
        return Iff(Call("claim"), quantified);
    }
}
