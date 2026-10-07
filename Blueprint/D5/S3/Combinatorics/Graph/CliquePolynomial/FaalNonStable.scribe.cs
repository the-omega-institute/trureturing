using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CliquePolynomial;

internal sealed class FaalNonStableDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/CliquePolynomial/FaalNonStable.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/teimoorifaal2026brestricted");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every r ≥ 1, the join of a complete graph on max(r−2,0) vertices with a four-cycle is r-connected, K_{r+3}-free and non-chordal. Marking one cycle vertex gives a clique polynomial with a zero in the product of the upper half-planes.",
        H("Non-chordal graphs with unstable restricted clique polynomials"),
        Blocks(
            Node("polynomial", "The restricted clique polynomial", "C_B", PolynomialFormula(),
                "Definition 2.1, page 4: \"For G=(V,E) and B ⊆ V, define\" C_B(G;x,y) := ∑_{K ⊆ V, K clique} x^{|K|} y^{|K ∩ B|}. Cliques are Mathlib SimpleGraph.IsClique on the set underlying a Finset. Finset.univ.powerset.filter enumerates every clique once, including the empty clique, which contributes 1 as in Example 2.3. The complex-valued function is evaluation of this real-coefficient polynomial.",
                AssessedProvenance.FromLiterature(Source)),
            Node("stability", "Real stability", "RealStable", StabilityFormula(),
                "Definition 2.4, page 4: \"A polynomial f(x,y) ∈ ℝ[x,y] is real stable if it is not identically zero and\" f(x,y) ≠ 0 \"for all (x,y) ∈ ℂ² such that Im(x) > 0 and Im(y) > 0.\" Here RealStable is this evaluation predicate on a function ℂ → ℂ → ℂ. It is applied to C_B, whose coefficients are real nonnegative integers. The first conjunct states that the function is not identically zero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("connectivity", "Vertex connectivity", "RConnected", ConnectivityFormula(),
                "Definition 4.2, page 7: \"A graph is r-connected if removal of fewer than r vertices leaves it connected.\" The finite graph also has more than r vertices, the standard vertex-connectivity size convention. Deletion is Mathlib SimpleGraph.induce on the set of vertices outside S; connectedness is SimpleGraph.Connected.",
                AssessedProvenance.FromLiterature(Source)),
            Node("chord", "A chord of a closed walk", "HasChord", ChordFormula(),
                "A chord joins two nonconsecutive vertices of the closed walk. Positions i and j are in Fin p.length, so the repeated terminal vertex is omitted. The inequality i.val + 1 < j.val orders the positions and excludes successive edges; the additional negation excludes the closing edge from the first to the last position. Walk.getVert takes a natural index: val explicitly displays the coercion from Fin p.length to ℕ.",
                AssessedProvenance.FromRepo(Source)),
            Node("chordality", "Chordal graphs", "Chordal", ChordalityFormula(),
                "Definition 4.3, page 7: \"A graph is chordal if every induced cycle has length 3.\" The same source, page 9, says \"every cycle of length >3 has a chord.\" The displayed definition uses the latter literal cycle-and-chord formulation. Cycles are Mathlib SimpleGraph.Walk.IsCycle, and every closed cycle of length at least four must have a chord.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Faal's existence question", "claim", ClaimFormula(),
                "Section 7, Open Problems, item 1, page 18: \"Necessity of Conditions: Are the conditions of r-connectivity and chordality also necessary? Is there an r-connected K_{r+3}-free non-chordal graph for which C_B(G;x,y) fails to be real-stable?\" The claim answers the second sentence for every natural r ≥ 1. V is a finite vertex type, G has decidable adjacency, and B is a Finset of vertices. Clique-freeness is Mathlib SimpleGraph.CliqueFree (r + 3); the final two conjuncts negate chordality and real stability.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("faal-result"), DeclarationHandle.Create(Prefix + "result"),
                H("A family for every positive connectivity"), StatementSource.FromAuthor(Disp(F.Id("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Put a = max(r−2,0), take G = K_a ∨ C₄, and mark the cycle vertex of index 0. Cliques of a join split uniquely into cliques of its two factors. The complete factor contributes (1+x)^a and the marked four-cycle contributes (1+2x)(1+x+xy). Thus C_B = (1+x)^a(1+2x)(1+x+xy), which vanishes at x=i and y=−1+i, both with imaginary part 1. After deletion of fewer than r vertices, a remaining complete-graph vertex connects all survivors; if no such vertex remains, at most one cycle vertex was deleted. The induced four-cycle has no chord, and every clique has size at most a+2 < r+3. Natural subtraction r−2 denotes max(r−2,0). For r=1 and r=2 the family is C₄; the assertion is r-connectedness and makes no exact-connectivity claim."))),
                DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("faal-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Qualified(string name)
    {
        var parts = name.Split('.');
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (tokens.Count != 0) tokens.Add(Dot);
            tokens.Add(part == "C_B" ? new Formula.Subscript(F.Id("C"), F.Id("B")) : F.Id(part));
        }
        return Seq([.. tokens]);
    }
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(Qualified(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(Qualified(name))), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula ExistsInstance(Formula type, Formula body) =>
        Seq(Exists, Sp, OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Instances(Formula body, params Formula[] types)
    {
        var tokens = new System.Collections.Generic.List<Formula>();
        foreach (var type in types)
            tokens.Add(Seq(OpenBracket, type, CloseBracket, Sp));
        tokens.Add(body);
        return Seq([.. tokens]);
    }
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula AtMost(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Not(Formula a) => new Formula.Not(Parenthesized(a));
    private static Formula PlusOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Vertex() => F.Id("V");
    private static Formula Graph() => Call("SimpleGraph", Vertex());
    private static Formula FinsetV() => Call("Finset", Vertex());
    private static Formula Walk() => Call("SimpleGraph.Walk", F.Id("G"), F.Id("v"), F.Id("v"));
    private static Formula Length() => Call("SimpleGraph.Walk.length", F.Id("p"));
    private static Formula ToSet(Formula k) => Parenthesized(Seq(k, Sp, Colon, Sp, Call("Set", Vertex())));
    private static Formula NotMember(Formula v, Formula s) => Not(Rel(v, FormulaRelationOperator.MemberOf, s));
    private static Formula LambdaOf(string v, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id(v), Sp, Colon, Sp, type)), Comma, Sp, body);

    private static Formula PolynomialFormula()
    {
        Formula k = F.Id("K"), b = F.Id("B"), x = F.Id("x"), y = F.Id("y");
        Formula cliques = Call("Finset.filter",
            Parenthesized(LambdaOf("K", FinsetV(), Call("SimpleGraph.IsClique", F.Id("G"),
                ToSet(k)))),
            Call("Finset.powerset", Parenthesized(Seq(Call("Finset.univ"), Sp, Colon, Sp, FinsetV()))));
        Formula weight = new Formula.Binary(new Formula.Power(x, Call("Finset.card", k)),
            FormulaBinaryOperator.Multiply,
            new Formula.Power(y, Call("Finset.card", Call("Finset.inter", k, b))));
        Formula sum = Seq(new Formula.Subscript(F.Sum, Seq(k, Sp, InMacro, Sp, cliques)), Sp, weight);
        return All("V", F.Id("Type"), Instances(All("G", Graph(), All("B", FinsetV(),
            All("x", Complexes(), All("y", Complexes(), Equal(Call("C_B", F.Id("G"), b, x, y), sum))))),
            Call("Fintype", Vertex()), Call("DecidableEq", Vertex())));
    }
    private static Formula StabilityFormula()
    {
        Formula f = F.Id("f"), x = F.Id("x"), y = F.Id("y");
        Formula ne = Rel(new Formula.Apply(f, [x, y]), FormulaRelationOperator.NotEqual, D(0));
        Formula nonzero = Some("x", Complexes(), Some("y", Complexes(), ne));
        Formula upper = All("x", Complexes(), All("y", Complexes(),
            Imp(Less(D(0), Call("Complex.im", x)), Imp(Less(D(0), Call("Complex.im", y)), ne))));
        return All("f", new Formula.TypeArrow(Complexes(), new Formula.TypeArrow(Complexes(), Complexes())),
            Iff(Call("RealStable", f), And(nonzero, upper)));
    }
    private static Formula ConnectivityFormula()
    {
        Formula s = F.Id("S"), r = F.Id("r");
        Formula survivors = Seq(OpenBrace, F.Id("v"), Sp, Bar, Sp, NotMember(F.Id("v"), s), CloseBrace);
        Formula deletion = All("S", FinsetV(), Imp(Less(Call("Finset.card", s), r),
            Call("SimpleGraph.Connected", Call("SimpleGraph.induce", F.Id("G"), survivors))));
        return All("V", F.Id("Type"), Instances(All("G", Graph(), All("r", Nats(),
            Iff(Call("RConnected", F.Id("G"), r), And(Less(r, Call("Fintype.card", Vertex())), deletion)))),
            Call("Fintype", Vertex())));
    }
    private static Formula ChordFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j");
        Formula iv = Call("val", i), jv = Call("val", j);
        Formula body = And(Less(PlusOf(iv, D(1)), jv),
            And(Not(And(Equal(iv, D(0)), Equal(PlusOf(jv, D(1)), Length()))),
                Call("SimpleGraph.Adj", F.Id("G"), Call("SimpleGraph.Walk.getVert", F.Id("p"), iv),
                    Call("SimpleGraph.Walk.getVert", F.Id("p"), jv))));
        return All("V", F.Id("Type"), All("G", Graph(), All("v", Vertex(), All("p", Walk(),
            Iff(Call("HasChord", F.Id("p")), Some("i", Call("Fin", Length()),
                Some("j", Call("Fin", Length()), body)))))));
    }
    private static Formula ChordalityFormula() => All("V", F.Id("Type"), All("G", Graph(),
        Iff(Call("Chordal", F.Id("G")), All("v", Vertex(), All("p", Walk(),
            Imp(Call("SimpleGraph.Walk.IsCycle", F.Id("p")),
                Imp(AtMost(D(4), Length()), Call("HasChord", F.Id("p")))))))));
    private static Formula ClaimFormula()
    {
        Formula g = F.Id("G"), b = F.Id("B"), r = F.Id("r");
        Formula properties = And(Call("RConnected", g, r),
            And(Call("SimpleGraph.CliqueFree", g, PlusOf(r, D(3))),
                And(Not(Call("Chordal", g)), Not(Call("RealStable", Call("C_B", g, b))))));
        Formula graphExists = Some("V", F.Id("Type"),
            ExistsInstance(Call("Fintype", Vertex()),
                ExistsInstance(Call("DecidableEq", Vertex()),
                    Some("G", Graph(), ExistsInstance(Call("DecidableRel", Qualified("G.Adj")),
                        Some("B", FinsetV(), properties))))));
        return Iff(F.Id("claim"), All("r", Nats(), Imp(AtMost(D(1), r), graphExists)));
    }
}
