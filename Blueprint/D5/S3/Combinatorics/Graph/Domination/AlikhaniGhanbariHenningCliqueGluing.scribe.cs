using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class AlikhaniGhanbariHenningCliqueGluingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/alikhanighanbarihenning2026strongdomination");
    private const string StrongDefinition = "A set D of vertices is a strong dominating set in a graph G, if for every vertex x ∈ V(G) \\ D there is a vertex y ∈ D with xy ∈ E(G) and deg(x) ≤ deg(y). The strong domination number γst(G) of G is the minimum cardinality of a strong dominating set in G.";
    private const string GluingDefinition = "Choose a clique of cardinality r from each Gi, i = 1, 2, and form a new graph G from the union of G1 and G2 by identifying the two chosen r-cliques in an arbitrary manner.";
    private const string Problem = "For r ≥ 2, let G1 and G2 be connected graphs both of order at least r + 1 that contain r-cliques A = {u1, u2, …, ur} and B = {v1, v2, …, vr}, respectively. Let Xi = NG1(ui) \\ A and Yi = NG2(vi) \\ B for i ∈ [r], and let ΣX,Y = Σ_{i=1}^r |Xi| + Σ_{i=1}^r |Yi|. Let G ∈ G1 ∪Kr G2 be obtained by a Kr-gluing of the graphs G1 and G2 by identifying the cliques A and B, where we identify the vertices ui and vi for i ∈ [r]. Determine a best possible lower bound on γst(G) in terms of γst(G1), γst(G2) and ΣX,Y. In particular, is it true that γst(G) ≥ γst(G1) + γst(G2) − 1 − ΣX,Y? (4)";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strong domination number of a clique gluing satisfies Inequality (4) of Alikhani, Ghanbari and Henning for every clique size at least two.",
        H("Strong domination under clique gluing"),
        Blocks(
            Node("IsStrongDominatingSet", "Strong dominating sets", StrongFormula(),
                "Abstract, p. 195: \"" + StrongDefinition + "\" Finite sets encode vertex subsets. SimpleGraph.degree counts each distinct neighbour once.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("strongDominationNumber", "The minimum cardinality", NumberFormula(),
                "Abstract, p. 195: \"" + StrongDefinition + "\" The full vertex set is strong dominating, so the natural-number infimum of attained sizes is attained.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("embedRight", "The second graph's vertex map", EmbedFormula(),
                "A vertex B i maps to Sum.inl (A i). A vertex outside the range of B maps to the right summand, with its proof of exclusion. Function.Embedding.invOfMemRange recovers the unique index in the range of B.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("glue", "The glued graph", GlueFormula(),
                "Section 1, p. 196: \"" + GluingDefinition + "\" The vertex type retains every vertex of G1 and exactly the vertices of G2 outside B. SimpleGraph.fromRel combines the two edge relations; repeated edges of the common clique occur once.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("X", "External neighbours of a clique vertex", XFormula(),
                "Problem 1, p. 202: \"" + Problem + "\" X G1 A i is Xi, and X G2 B i is Yi. Finset.univ.map A is the enumerated clique. Index i in Fin r corresponds to index i+1 in the paper.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("sigmaXY", "The total external-neighbour count", SigmaFormula(),
                "Problem 1, p. 202: \"" + Problem + "\" Each cardinality is counted separately for each clique vertex; a vertex adjacent to several clique vertices contributes several times.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Inequality (4) on the whole stated domain", Disp(Iff(X("claim"), Parenthesized(ClaimBody()))),
                "Problem 1, p. 202: \"" + Problem + "\" The displayed proposition answers the final question affirmatively. The two graph orders are Fintype.card, the cliques are the ranges of embeddings from Fin r, and all subtraction is in the integers. Adjacency of the glued graph is decided classically.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "The lower bound for every r at least two", Disp(ClaimBody()),
                "Restrict a minimum strong dominating set to each graph outside the common clique. In each factor, add a clique vertex of maximum degree; it strongly dominates the rest of the clique. If the original set meets the clique, also add the external neighbours of that clique. Every remaining exterior vertex keeps its original dominator and degree comparison. The two restrictions then have total size at most the original size plus one plus sigmaXY: a selected clique vertex pays for one of the two added clique vertices. If the original set misses the clique, connectedness and the proper clique range give at least one external neighbour, which pays for the extra vertex. Taking minimum sizes and rearranging in the integers yields the displayed bound. General sharpness of the source family and bounds using finer parameters are not asserted.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("alikhani-ghanbari-henning-clique-gluing-problem-1"),
                    ResolutionKind.Proved))), []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("agh-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula X(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Eqf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula Z => new Formula.Integers();
    private static Formula Inst(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Range(Formula a) => App(Q("Set", "range"), a);
    private static Formula Fin(Formula r) => Call("Fin", r);
    private static Formula Emb(Formula a, Formula b) => App(Q("Function", "Embedding"), a, b);
    private static Formula Adj(Formula g, Formula x, Formula y) => App(Q("SimpleGraph", "Adj"), g, x, y);
    private static Formula Degree(Formula g, Formula x) => App(Q("SimpleGraph", "degree"), g, x);
    private static Formula Card(Formula s) => App(Q("Finset", "card"), s);
    private static Formula DecAdj(Formula g, Formula body) => Inst(Call("DecidableRel", App(Q("SimpleGraph", "Adj"), g)), body);
    private static Formula Pair(Formula a, Formula b) => Seq(Langle, Sp, a, Comma, Sp, b, Rangle);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Operatorname, Grp(X("fun")), Sp, Parenthesized(Seq(X(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula SetOf(string name, Formula type, Formula predicate) =>
        Seq(OpenBrace, Sp, X(name), Sp, Colon, Sp, type, Sp, Mid, Sp, predicate, Sp, CloseBrace);
    private static Formula Carrier(Formula v1, Formula v2, Formula b) =>
        Call("Sum", v1, SetOf("w", v2, new Formula.Not(Mem(X("w"), Range(b)))));

    private static Formula StrongFormula()
    {
        Formula v = X("V"), g = X("G"), d = X("D"), x = X("x"), y = X("y");
        Formula rhs = All("x", v, Imp(new Formula.Not(Mem(x, d)), Some("y", v,
            And(Mem(y, d), And(Adj(g, x, y), Le(Degree(g, x), Degree(g, y)))))));
        return Disp(All("V", X("Type"), Inst(Call("Fintype", v), All("G", Call("SimpleGraph", v),
            DecAdj(g, All("D", Call("Finset", v), Iff(Call("IsStrongDominatingSet", g, d), Parenthesized(rhs))))))));
    }

    private static Formula NumberFormula()
    {
        Formula v = X("V"), g = X("G"), k = X("k"), d = X("D");
        Formula sizes = SetOf("k", Nat, Some("D", Call("Finset", v),
            And(Call("IsStrongDominatingSet", g, d), Eqf(Card(d), k))));
        return Disp(All("V", X("Type"), Inst(Call("Fintype", v), All("G", Call("SimpleGraph", v),
            DecAdj(g, Eqf(Call("strongDominationNumber", g), Call("sInf", sizes)))))));
    }

    private static Formula EmbedFormula()
    {
        Formula r = X("r"), v1 = X("V1"), v2 = X("V2"), a = X("A"), b = X("B"), w = X("w"), h = X("h");
        Formula inv = Seq(Operatorname, Grp(X("Function")), Dot, Operatorname, Grp(X("Embedding")), Dot, Operatorname, Grp(X("invOfMemRange")));
        Formula rhs = Seq(Operatorname, Grp(X("if")), Sp, h, Sp, Colon, Sp, Mem(w, Range(b)), Sp,
            Operatorname, Grp(X("then")), Sp, App(Q("Sum", "inl"), App(a, App(inv, b, Pair(w, h)))), Sp,
            Operatorname, Grp(X("else")), Sp, App(Q("Sum", "inr"), Pair(w, h)));
        return Disp(All("r", Nat, All("V1", X("Type"), All("V2", X("Type"),
            Inst(Call("DecidableEq", v2), All("A", Emb(Fin(r), v1), All("B", Emb(Fin(r), v2),
                All("w", v2, Eqf(Call("embedRight", a, b, w), Parenthesized(rhs))))))))));
    }

    private static Formula GlueFormula()
    {
        Formula r = X("r"), v1 = X("V1"), v2 = X("V2"), g1 = X("G1"), g2 = X("G2"), a = X("A"), b = X("B"), p = X("p"), q = X("q"), x = X("x"), y = X("y");
        Formula left = Some("x", v1, Some("y", v1, And(Eqf(p, App(Q("Sum", "inl"), x)),
            And(Eqf(q, App(Q("Sum", "inl"), y)), Adj(g1, x, y)))));
        Formula right = Some("x", v2, Some("y", v2, And(Eqf(p, Call("embedRight", a, b, x)),
            And(Eqf(q, Call("embedRight", a, b, y)), Adj(g2, x, y)))));
        Formula rhs = App(Q("SimpleGraph", "fromRel"), Lambda("p", Carrier(v1, v2, b), Lambda("q", Carrier(v1, v2, b), Or(left, right))));
        return Disp(TwoGraphs(Eqf(Call("glue", g1, g2, a, b), rhs), false));
    }

    private static Formula XFormula()
    {
        Formula r = X("r"), v = X("V1"), g = X("G1"), a = X("A"), i = X("i");
        Formula rhs = Seq(App(Q("SimpleGraph", "neighborFinset"), g, App(a, i)), Sp, Setminus, Sp,
            App(Q("Finset", "map"), a, Q("Finset", "univ")));
        return Disp(All("r", Nat, All("V1", X("Type"), Inst(Call("Fintype", v), Inst(Call("DecidableEq", v),
            All("G1", Call("SimpleGraph", v), DecAdj(g, All("A", Emb(Fin(r), v),
                All("i", Fin(r), Eqf(Call("X", g, a, i), rhs))))))))));
    }

    private static Formula SigmaFormula()
    {
        Formula r = X("r"), i = X("i"), g1 = X("G1"), g2 = X("G2"), a = X("A"), b = X("B");
        Formula SumX(Formula g, Formula c) => Parenthesized(Seq(Sum, Underscore,
            Grp(Seq(i, Sp, Colon, Sp, Fin(r))), Sp, Card(Call("X", g, c, i))));
        return Disp(TwoGraphs(Eqf(Call("sigmaXY", g1, g2, a, b), Add(SumX(g1, a), SumX(g2, b))), true));
    }

    private static Formula TwoGraphs(Formula body, bool finite)
    {
        Formula r = X("r"), v1 = X("V1"), v2 = X("V2"), g1 = X("G1"), g2 = X("G2");
        Formula tail = All("G1", Call("SimpleGraph", v1), All("G2", Call("SimpleGraph", v2),
            All("A", Emb(Fin(r), v1), All("B", Emb(Fin(r), v2), body))));
        if (finite) tail = All("G1", Call("SimpleGraph", v1), DecAdj(g1,
            All("G2", Call("SimpleGraph", v2), DecAdj(g2,
                All("A", Emb(Fin(r), v1), All("B", Emb(Fin(r), v2), body))))));
        Formula instances = finite ? Inst(Call("Fintype", v1), Inst(Call("DecidableEq", v1),
            Inst(Call("Fintype", v2), Inst(Call("DecidableEq", v2), tail)))) : Inst(Call("DecidableEq", v2), tail);
        return All("r", Nat, All("V1", X("Type"), All("V2", X("Type"), instances)));
    }

    private static Formula ClaimBody()
    {
        Formula r = X("r"), v1 = X("V1"), v2 = X("V2"), g1 = X("G1"), g2 = X("G2"), a = X("A"), b = X("B");
        Formula IntCast(Formula n) => Parenthesized(Seq(n, Sp, Colon, Sp, Z));
        Formula lhs = Sub(Sub(Add(IntCast(Call("strongDominationNumber", g1)), IntCast(Call("strongDominationNumber", g2))), D(1)),
            IntCast(Call("sigmaXY", g1, g2, a, b)));
        Formula bound = Le(lhs, IntCast(Call("strongDominationNumber", Call("glue", g1, g2, a, b))));
        Formula hypotheses = Imp(App(Q("SimpleGraph", "Connected"), g1), Imp(App(Q("SimpleGraph", "Connected"), g2),
            Imp(Le(Add(r, D(1)), App(Q("Fintype", "card"), v1)), Imp(Le(Add(r, D(1)), App(Q("Fintype", "card"), v2)),
                Imp(App(Q("SimpleGraph", "IsClique"), g1, Range(a)), Imp(App(Q("SimpleGraph", "IsClique"), g2, Range(b)), bound))))));
        Formula tail = All("G1", Call("SimpleGraph", v1), All("G2", Call("SimpleGraph", v2),
            All("A", Emb(Fin(r), v1), All("B", Emb(Fin(r), v2), hypotheses))));
        return All("r", Nat, Imp(Le(D(2), r), All("V1", X("Type"), All("V2", X("Type"),
            Inst(Call("Fintype", v1), Inst(Call("DecidableEq", v1), Inst(Call("Fintype", v2), Inst(Call("DecidableEq", v2), tail))))))));
    }
}
