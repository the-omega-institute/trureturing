using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.EdgeLabeling;

internal sealed class AceskaLortRippergerSparsest14Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/EdgeLabeling/AceskaLortRippergerSparsest14.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/aceskalortripperger2026ornaments");
    private const string LabelingQuote =
        "Section 1.1, page 2: “A difference distance magic (DDM) labeling [2] of an oriented graph G⃗ "
        + "with n vertices is a bijection f: V(G⃗) → {1,2,...,n} where there exists some k ∈ ℕ "
        + "such that for all x ∈ V(G⃗) wt_f(x)=k; it shows that k=0 for all x ∈ V(G⃗).” ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A connected 14-vertex DDMOG with 23 edges refutes the proposed 24-edge lower bound.",
        H("A connected 23-edge DDMOG on fourteen vertices"),
        Blocks(
            Node("weight", "Incoming label sum minus outgoing label sum", WeightFormula(),
                "Section 1.1, page 2: “The weight of vertex x is defined [2] as the sum of the vertex "
                + "labels directed into x minus the sum of vertex labels directed out of x,” followed by "
                + "wt(x) = ∑_{y∈N⁺(x)} f(y) − ∑_{y∈N⁻(x)} f(y). "
                + "Page 1: “The in-neighborhood of a vertex v is the set of vertices u ∈ V(D) such that "
                + "(u,v) ∈ E(D) and is denoted N⁺(v).” The out-neighborhood uses (v,u). "
                + "Both sums run over the finite vertex type, with zero outside the relevant set. "
                + "Labels and weights are integers.", AssessedProvenance.FromLiterature(Source)),
            Node("IsConsecutiveLabeling", "Bijection onto the consecutive integer labels", ConsecutiveFormula(),
                LabelingQuote + "This predicate expresses the bijection clause using Set.BijOn. "
                + "The interval endpoints and the cardinality cast have type Int.",
                AssessedProvenance.FromLiterature(Source)),
            Node("IsDDMLabeling", "Consecutive labels with a common natural weight", DdmFormula(),
                LabelingQuote + "The common constant k remains existential and natural; "
                + "its occurrence in the integer weight equality is coerced to Int.",
                AssessedProvenance.FromLiterature(Source)),
            Node("edgeCount", "Number of directed edges", EdgeCountFormula(),
                "Section 1.1, page 1: “A digraph D is a graph with directed edges: it is defined to be "
                + "a pair (V,E), consisting of a set of vertices V(D) and a collection of ordered pairs "
                + "of vertices E(D), called edges.” This cardinality counts ordered adjacent pairs. "
                + "For an oriented graph there are no loops or opposite arcs, so it also counts "
                + "the underlying undirected edges.", AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The fourteen-vertex minimality conjecture", Iff(Name("claim"), ClaimBody()),
                "Conclusion, page 25: “Another question we have encountered as we were writing this paper "
                + "is related to the minimal number of edges a connected DDMOG with n vertices must have: "
                + "What is the sparsest connected DDMOG with n vertices in terms of edges? When observing "
                + "the DDMOG with 14 vertices in Figure 6, we conjecture that it is the sparsest DDMOG "
                + "with 14 vertices.” Remark 2, page 9, counts 24 edges in Figure 6. "
                + "Fin 14 indexes the vertices from zero; Std.Asymm excludes loops and opposite arcs. "
                + "SimpleGraph.fromRel gives the undirected graph, and Connected is its usual "
                + "connectedness. The asserted lower bound is 24 for every consecutive DDM labeling.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("alr-sparsest-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The 24-edge lower bound is false"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("On Fin 14, label vertex i by its integer value plus one. "
                    + "The 23 arcs are (0,4), (0,11), (1,4), (1,10), (2,8), (3,2), (3,12), (4,2), "
                    + "(5,3), (5,9), (6,1), (6,11), (7,0), (7,10), (8,0), (8,1), (9,3), (9,12), "
                    + "(10,9), (11,7), (12,13), (13,5), (13,6). Incoming and outgoing label sums "
                    + "agree at every vertex. A spanning tree connects all fourteen vertices. "
                    + "There are no loops or opposite arcs, and the label interval is exactly 1 through 14. "
                    + "Thus a connected DDMOG has 23 edges, contradicting the asserted lower bound. "
                    + "This gives no lower bound excluding 21 or 22 edges and no general minimum formula."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("op-alr2606sparse"), ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("alr-sparsest-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Name(string value) => Seq(Operatorname, Grp(F.Id(value)));
    private static Formula Q(string owner, string name) => Seq(Name(owner), Dot, Name(name));
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Name(name), args);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula CastInt(Formula a) => Parenthesized(Seq(a, Sp, Colon, Sp, F.Id("Int")));
    private static Formula Adj(Formula d, Formula u, Formula v) => App(Q("Digraph", "Adj"), d, u, v);
    private static Formula WithFinite(Formula v, Formula body) =>
        Seq(OpenBracket, Call("Fintype", v), CloseBracket, Sp, body);
    private static Formula SetOf(string name, Formula type, Formula condition) =>
        Seq(OpenBrace, F.Id(name), Sp, Colon, Sp, type, Sp, Bar, Sp, condition, CloseBrace);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body);

    private static Formula WeightFormula()
    {
        var v = F.Id("V"); var d = F.Id("D"); var f = F.Id("f"); var x = F.Id("x"); var y = F.Id("y");
        Formula SumTerm(bool incoming)
        {
            var set = SetOf("y", v, incoming ? Adj(d, y, x) : Adj(d, x, y));
            var member = new Formula.Relation(y, FormulaRelationOperator.MemberOf, set);
            var term = Seq(Name("if"), Sp, member, Sp, Name("then"), Sp, App(f, y), Sp, Name("else"), Sp, D(0));
            return Seq(new Formula.Subscript(Sum, Seq(y, Sp, Colon, Sp, v)), Sp, Parenthesized(term));
        }
        return All("V", F.Id("Type"), WithFinite(v, All("D", Call("Digraph", v),
            All("f", Fn(v, F.Id("Int")), All("x", v,
                Eqn(Call("weight", d, f, x), new Formula.Binary(SumTerm(true), FormulaBinaryOperator.Subtract, SumTerm(false))))))));
    }

    private static Formula ConsecutiveFormula()
    {
        var v = F.Id("V"); var f = F.Id("f");
        var interval = App(Q("Set", "Icc"), CastInt(D(1)), CastInt(App(Q("Fintype", "card"), v)));
        return All("V", F.Id("Type"), WithFinite(v, All("f", Fn(v, F.Id("Int")),
            Iff(Call("IsConsecutiveLabeling", f), App(Q("Set", "BijOn"), f, Q("Set", "univ"), interval)))));
    }

    private static Formula DdmFormula()
    {
        var v = F.Id("V"); var d = F.Id("D"); var f = F.Id("f"); var x = F.Id("x");
        return All("V", F.Id("Type"), WithFinite(v, All("D", Call("Digraph", v), All("f", Fn(v, F.Id("Int")),
            Iff(Call("IsDDMLabeling", d, f), And(Call("IsConsecutiveLabeling", f),
                Some("k", F.Id("Nat"), All("x", v, Eqn(Call("weight", d, f, x), CastInt(F.Id("k")))))))))));
    }

    private static Formula EdgeCountFormula()
    {
        var v = F.Id("V"); var d = F.Id("D"); var e = F.Id("e");
        var pair = Seq(v, Sp, Times, Sp, v);
        var subtype = Seq(OpenBrace, e, Sp, Colon, Sp, pair, Sp, Slash, Slash, Sp,
            Adj(d, Seq(e, Dot, D(1)), Seq(e, Dot, D(2))), CloseBrace);
        return All("V", F.Id("Type"), WithFinite(v, All("D", Call("Digraph", v),
            Eqn(Call("edgeCount", d), App(Q("Fintype", "card"), subtype)))));
    }

    private static Formula ClaimBody()
    {
        var v = Call("Fin", D(1, 4)); var d = F.Id("D"); var f = F.Id("f"); var u = F.Id("u"); var w = F.Id("v");
        var relation = Lambda("u", v, Lambda("v", v, Or(Adj(d, u, w), Adj(d, w, u))));
        var connected = App(Q("SimpleGraph", "Connected"), App(Q("SimpleGraph", "fromRel"), Parenthesized(relation)));
        return All("D", Call("Digraph", v), All("f", Fn(v, F.Id("Int")),
            Imp(App(Q("Std", "Asymm"), App(Q("Digraph", "Adj"), d)),
                Imp(connected, Imp(Call("IsDDMLabeling", d, f), Leq(D(2, 4), Call("edgeCount", d)))))));
    }
}
