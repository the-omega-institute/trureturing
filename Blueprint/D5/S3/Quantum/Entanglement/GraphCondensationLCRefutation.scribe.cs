using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class GraphCondensationLCRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/GraphCondensationLCRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/vandre2024marginals");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two connected six-vertex graphs are related by local complementations and satisfy the bound of at most one outside neighbour for every vertex of the condensation set in both graphs, but their condensed graphs are not LC-equivalent. This refutes Conjecture 16 of Vandré, de Jong, Hahn, Burchardt, Gühne and Pappa.",
        H("Condensation need not preserve LC-equivalence"),
        Blocks(
            Node("condense", "Condensed graph", CondenseFormula(),
                "Definition 13 (arXiv:2406.09956v2, p. 12): “Consider a graph G = (V, E) and a set C ⊆ V. The condensed graph G_C = (V_C, E_C) consists of the node set V_C = {c} ∪ (V \\ C) and edge set E_C defined in the following way: (i, j) ∈ E_C if either i, j ∈ V \\ C and (i, j) ∈ E, or j = c and there exists s ∈ C such that (i, s) ∈ E.” The fresh vertex c is none; an outside vertex is some(i), where i is a subtype element with val(i) ∉ C. The undirected adjacency is symmetrized, and none is not adjacent to itself. The graph type and the four adjacency cases below are the defining expression.",
                "condense", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("equivalent", "Finite sequences of local complementations", EquivalentFormula(),
                "LC-equivalence is existence of a finite list s of vertices such that H = lcSeq(G, s). Local complementation complements the edges between the selected vertex's neighbours and preserves all other edges. The reused lcSeq applies these operations in list order. The paper states (p. 5): “There is a one-to-one correspondence between the local complementation orbit of a given graph and the orbit under local Clifford operations of the corresponding graph state.” Definition 4 (pp. 4–5) gives the local complementation formula; the correspondence cites Van den Nest, Dehaene and De Moor (2004).",
                "LCEquivalent", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 16", ClaimFormula(),
                "Conjecture 16 (arXiv:2406.09956v2, p. 13): “Given two graphs G and G′ and a condensation set C such that each node in C is connected to at most one node in the neighborhood in V \\ C. If G and G′ are LC-equivalent, it follows that G_c and G′_c are LC-equivalent.” V is any finite labelled vertex type with decidable equality, G and H encode G and G′, and C is a finset. The bracketed [Fintype V] and [DecidableEq V] terms are the anonymous Lean typeclass assumptions. Both graphs are connected, as the paper assumes for its simple graphs. The outside-neighbour bound is required in both graphs: the cardinality of {i in V | i ∉ C and Adj(G, s, i)} is at most one for every s ∈ C, and likewise for H. The function filter selects precisely these vertices from univ; card is finset cardinality. This reading meets the degree condition on both sides.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Six vertices refute the conjecture", Disp(new Formula.Not(F.Id("claim"))),
                "On Fin(6), take C = {0, 1, 2}, E(G) = {01, 02, 05, 14, 23} and E(H) = {05, 14, 23, 35, 45}. Both graphs are connected and each vertex of C has exactly one outside neighbour. Complementing at 0, 1, 2, 3, 4, 5 in order maps G to H. Condensation gives Mathlib's star graph with centre none and leaves 3, 4, 5, and the diamond with edges {c3, c4, c5, 35, 45}. The family consisting of the complete graph and every star is closed under local complementation: at a star's centre it gives the complete graph, at a leaf it preserves the star, and at a vertex of the complete graph it gives the star centred there. Induction over the list of operations keeps the condensed first graph in this family. The diamond is neither complete nor any of the four stars, as specific adjacency comparisons show, so it cannot be reached. On four vertices the family's graphs have three or six edges, while the diamond has five.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("vandre-2024-graph-condensation-lc-equivalence-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("condenselc-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Ex(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Member(Formula a, Formula set) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, set);
    private static Formula Adj(Formula graph, Formula a, Formula b) => Call("Adj", graph, a, b);
    private static Formula OutsideType() =>
        Seq(OpenBrace, F.Id("v"), Colon, Sp, F.Id("V"), Sp, Mid, Sp,
            new Formula.Not(Parenthesized(Member(F.Id("v"), F.Id("C")))), CloseBrace);

    private static Formula CondenseFormula()
    {
        Formula g = F.Id("G"), c = F.Id("C"), i = F.Id("i"), j = F.Id("j"), s = F.Id("s");
        Formula gc = Call("condense", g, c), none = Named("none");
        Formula vi = Call("val", i), vj = Call("val", j);
        Formula neighbours = Ex("s", F.Id("V"), And(Member(s, c), Adj(g, vi, s)));
        Formula rows = new Formula.Aligned([
            Seq(gc, Colon, Sp, Call("SimpleGraph", Call("Option", OutsideType()))),
            Iff(Adj(gc, none, none), Named("False")),
            All("i", OutsideType(), All("j", OutsideType(),
                Iff(Adj(gc, Call("some", i), Call("some", j)), Adj(g, vi, vj)))),
            All("i", OutsideType(), Iff(Adj(gc, Call("some", i), none), neighbours)),
            All("i", OutsideType(), Iff(Adj(gc, none, Call("some", i)), neighbours))]);
        return Disp(All("V", Named("Type"), All("G", Call("SimpleGraph", F.Id("V")),
            All("C", Call("Finset", F.Id("V")), rows))));
    }

    private static Formula EquivalentFormula()
    {
        Formula relation = Iff(Call("LCEquivalent", F.Id("G"), F.Id("H")),
            Ex("s", Call("List", F.Id("V")),
                Equal(F.Id("H"), Call("lcSeq", F.Id("G"), F.Id("s")))));
        return Disp(All("V", Named("Type"),
            All("G", Call("SimpleGraph", F.Id("V")),
                All("H", Call("SimpleGraph", F.Id("V")), relation))));
    }

    private static Formula Bound(Formula g)
    {
        Formula s = F.Id("s"), i = F.Id("i"), c = F.Id("C");
        Formula predicate = Seq(i, Sp, Mapsto, Sp,
            Parenthesized(And(new Formula.Not(Parenthesized(Member(i, c))), Adj(g, s, i))));
        Formula count = Call("card", Call("filter", Named("univ"), predicate));
        return All("s", F.Id("V"), Implies(Member(s, c),
            new Formula.Relation(count, FormulaRelationOperator.LessThanOrEqual, D(1))));
    }

    private static Formula ClaimFormula()
    {
        Formula v = F.Id("V"), g = F.Id("G"), h = F.Id("H"), c = F.Id("C");
        Formula conclusion = Call("LCEquivalent", Call("condense", g, c), Call("condense", h, c));
        Formula body = Implies(Call("Connected", g), Implies(Call("Connected", h),
            Implies(Bound(g), Implies(Bound(h), Implies(Call("LCEquivalent", g, h), conclusion)))));
        body = All("G", Call("SimpleGraph", v), All("H", Call("SimpleGraph", v),
            All("C", Call("Finset", v), body)));
        body = Seq(Forall, Sp, Parenthesized(Seq(v, Colon, Sp, Named("Type"))), Sp,
            OpenBracket, Call("Fintype", v), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", v), CloseBracket, Comma, Sp, body);
        return Disp(Iff(F.Id("claim"), body));
    }
}
