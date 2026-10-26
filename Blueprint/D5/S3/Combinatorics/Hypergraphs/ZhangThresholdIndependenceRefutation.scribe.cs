using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hypergraphs;

internal sealed class ZhangThresholdIndependenceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hypergraphs/ZhangThresholdIndependenceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/zhang2023thresholdindependence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two five-vertex T2 hypergraphs share an independence polynomial but are not isomorphic.",
        H("Independence polynomials do not determine T2-threshold hypergraphs"),
        Blocks(
            Node("hypergraph", "Finite uniform hypergraphs", "KHypergraph", HypergraphFormula(),
                "Zhang, arXiv:2303.01024v1, p. 2: “A hypergraph H = (V, E) is an order pair of a set of vertices V and a set of hyperedges E, where each hyperedge e ∈ E is a non-empty subset of the vertex set V. Further, if |e| = k for any e ∈ E, then H is called k-uniform hypergraph, k-hypergraph or k-families.” The finite vertex type is V; edges is a finite set of finite vertex subsets, and uniform requires each edge to have k vertices. The record schema below displays both fields. The question is refuted at k = 3, where all edges are nonempty; the encoding also permits the unused values k = 0, 1, 2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("independent", "Independent vertex subsets", "IsIndependent", IndependentFormula(),
                "Zhang, p. 3: “Motivated by this idea, a vertex subset W ⊆ V is called an independent set in a hypergraph H = (V, E) if W does not include any hyperedges, i.e., ∀e ∈ E, e ⊄ W.” The variable S denotes this vertex subset. Independence excludes containment of every edge, including for the empty subset.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("polynomial", "The independence polynomial", "indepPoly", PolynomialFormula(),
                "Zhang, p. 3, Eq. (8): “Given a hypergraph H = (V, E), the independence polynomial I(H; x) of H is defined as [13]” followed by I(H; x) = Σ_{W ⊆ V is independent in H} x^{|W|}. The sum includes the empty independent set. Polynomial.X is the formal indeterminate over ℤ, and Finset.univ enumerates all finite subsets of V, each once.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("threshold", "The T2-threshold property", "IsT2Threshold", ThresholdFormula(),
                "Zhang, p. 12, Definition 4.1 (T2): “There exist a labeling c′ of V and a threshold τ′ such that, for any vertex subset X ⊆ V of size k, X ∈ E if and only if Σ_{x∈X} c′(x) > τ′.” Here c and t are real-valued labels and a real threshold; only subsets with exactly k vertices are tested, and the inequality is strict.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("isomorphism", "Isomorphism by a vertex bijection", "Isomorphic", IsomorphicFormula(),
                "The vertex equivalence s maps each finite edge using s.toEmbedding. The equivalence of membership requires this map to carry the entire edge set onto the other edge set, with the inverse vertex equivalence providing the reverse map.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The positive answer to the closing question", "claim",
                Disp(IffFormula(Named("claim"), Parenthesized(ClaimBody()))),
                "Zhang, p. 18, Section 5: “One remaining question here is about the uniqueness of the independence polynomials of antiregular k-hypergraphs. Alternatively, a more general question is, given two T2-threshold k-hypergraphs with the same independence polynomial, are they isomorphic? These are left for future work.” The positive answer is expressed as the universal implication below over all finite vertex types V and W. A pair with k = 3 suffices to answer the question negatively within the paper's k ≥ 3 range. The narrower antiregular question is separate.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "A five-vertex counterexample", "result",
                Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "On Fin 5, take all triples except {0,1,2}, {0,1,3}, {0,1,4} for the first hypergraph, and all triples except {0,1,2}, {0,1,3}, {0,2,3} for the second. The first labels are (0,0,1,1,1) with threshold 1; the second labels are (0,1,1,1,3) with threshold 2. Each hypergraph has exactly the empty independent set, the five singletons, the ten pairs, and its three missing triples. Hence their independence polynomials coincide. Vertex 2 of the first has degree 5; no vertex of the second has degree 5. A vertex bijection preserving edges preserves these incidence counts, so an isomorphism is impossible. This answers the general T2 question at five vertices. The arbitrary-size family, the antiregular identification and the T1 question are not established here. The source's formulas and threshold theorems do not require a positive answer to this closing question.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhang-2026-threshold-hypergraph-independence-polynomial"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("zhang-threshold-independence-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula Member(Formula value, string field) => Seq(value, Dot, Named(field));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula InSet(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula ImpliesFormula(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffFormula(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula InstanceBinders(Formula v) =>
        Seq(OpenBracket, Call("Fintype", v), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", v), CloseBracket);
    private static Formula VertexType(string name, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, Named("Type"))), Sp,
            InstanceBinders(F.Id(name)), Comma, Sp, body);
    private static Formula Context(Formula body) =>
        All("k", Seq(Mathbb, Grp(F.Id("N"))), VertexType("V", body));
    private static Formula HypergraphType(Formula v) => Call("KHypergraph", F.Id("k"), v);
    private static Formula FinsetType(Formula v) => Call("Finset", v);
    private static Formula Card(Formula s) => App(Q("Finset", "card"), s);

    private static Formula HypergraphFormula()
    {
        Formula v = F.Id("V"), edges = F.Id("edges"), e = F.Id("e");
        Formula uniform = All("e", FinsetType(v), ImpliesFormula(InSet(e, edges), Equal(Card(e), F.Id("k"))));
        return Disp(Context(Equal(HypergraphType(v), Seq(OpenBrace, F.Id("edges"), Colon, Sp,
            FinsetType(FinsetType(v)), Comma, Sp, Named("uniform"), Colon, Sp, uniform, CloseBrace))));
    }

    private static Formula IndependentFormula()
    {
        Formula v = F.Id("V"), h = F.Id("H"), s = F.Id("S"), e = F.Id("e");
        Formula body = All("e", FinsetType(v), ImpliesFormula(InSet(e, Member(h, "edges")),
            new Formula.Not(Parenthesized(Seq(e, Sp, Subseteq, Sp, s)))));
        return Disp(Context(All("H", HypergraphType(v), All("S", FinsetType(v),
            IffFormula(Call("IsIndependent", h, s), Parenthesized(body))))));
    }

    private static Formula PolynomialFormula()
    {
        Formula v = F.Id("V"), h = F.Id("H"), s = F.Id("S");
        Formula subsets = Parenthesized(Seq(Q("Finset", "univ"), Colon, Sp, FinsetType(FinsetType(v))));
        Formula predicate = Parenthesized(Seq(Named("fun"), Sp, s, Sp, Mapsto, Sp, Call("IsIndependent", h, s)));
        Formula family = App(Q("Finset", "filter"), predicate, subsets);
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(s, Sp, InMacro, Sp, family)), Sp,
            new Formula.Power(Q("Polynomial", "X"), Card(s)));
        return Disp(Context(All("H", HypergraphType(v), Equal(Parenthesized(Seq(Call("indepPoly", h), Colon, Sp, Call("Polynomial", new Formula.Integers()))), sum))));
    }

    private static Formula ThresholdFormula()
    {
        Formula v = F.Id("V"), h = F.Id("H"), x = F.Id("X"), c = F.Id("c"), t = F.Id("t"), a = F.Id("a");
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(a, Sp, InMacro, Sp, x)), Sp, App(c, a));
        Formula test = All("X", FinsetType(v), ImpliesFormula(Equal(Card(x), F.Id("k")),
            IffFormula(InSet(x, Member(h, "edges")), new Formula.Relation(t, FormulaRelationOperator.LessThan, sum))));
        Formula body = Some("c", Arrow(v, Seq(Mathbb, Grp(F.Id("R")))), Some("t", Seq(Mathbb, Grp(F.Id("R"))), test));
        return Disp(Context(All("H", HypergraphType(v),
            IffFormula(Call("IsT2Threshold", h), Parenthesized(body)))));
    }

    private static Formula IsomorphicFormula()
    {
        Formula v = F.Id("V"), w = F.Id("W"), h = F.Id("H"), j = F.Id("J"), s = F.Id("s"), e = F.Id("e");
        Formula mapped = App(Q("Finset", "map"), Member(s, "toEmbedding"), e);
        Formula body = Some("s", Call("Equiv", v, w), All("e", FinsetType(v),
            IffFormula(InSet(e, Member(h, "edges")), InSet(mapped, Member(j, "edges")))));
        return Disp(Context(VertexType("W",
            All("H", HypergraphType(v), All("J", HypergraphType(w),
                IffFormula(Call("Isomorphic", h, j), Parenthesized(body)))))));
    }

    private static Formula ClaimBody()
    {
        Formula v = F.Id("V"), w = F.Id("W"), h = F.Id("H"), j = F.Id("J");
        Formula body = ImpliesFormula(Call("IsT2Threshold", h),
            ImpliesFormula(Call("IsT2Threshold", j),
                ImpliesFormula(Equal(Call("indepPoly", h), Call("indepPoly", j)), Call("Isomorphic", h, j))));
        return Seq(Forall, Sp,
            Parenthesized(Seq(F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp,
            Parenthesized(Seq(v, Colon, Sp, Named("Type"))), Sp,
            Parenthesized(Seq(w, Colon, Sp, Named("Type"))), Sp,
            InstanceBinders(v), Sp, InstanceBinders(w), Comma, Sp,
            All("H", HypergraphType(v), All("J", HypergraphType(w), body)));
    }
}
