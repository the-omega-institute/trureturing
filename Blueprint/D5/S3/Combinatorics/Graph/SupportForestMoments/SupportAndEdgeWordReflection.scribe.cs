using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.SupportForestMoments;

internal sealed class SupportAndEdgeWordReflectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/shapiro2026spectrum");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Support counts and sound reflection of edge-word character moments.", H("Support forests and edge-word reflection"),
        Blocks(
            Def("endpointSet", "Endpoint set", EndpointSetFormula(), "The union of the endpoint sets of the unordered edges. Loops, if supplied as raw symmetric pairs, contribute their one endpoint."),
            Def("endpointGraph", "Graph on the endpoints", EndpointGraphFormula(), "The graph from the supplied edge set is induced on exactly its endpoints. This induction changes the vertex carrier; it does not impose ambient inducedness."),
            Def("N_H", "Support-subgraph count", CountFormula(), "Section 6.1, page 5: \"For a finite simple graph H without isolated vertices, let N_H(G) denote the number of edge subsets S ⊆ E(G) for which the graph with edge set S and vertex set formed by the endpoints of S is isomorphic to H. No inducedness condition is imposed on the ambient graph G.\" Vertices are Fin n and Fin h; each edge subset is counted once, independently of how many isomorphisms it admits.", true),
            Def("c1", "Fixed points", CycleCountFormula(false), "Section 6, page 4: \"If σ ∈ Sₙ, let c₁(σ) be the number of fixed points of σ and let c₂(σ) be the number of two-cycles in its cycle decomposition.\" The encoding names these counts c1 and c2. The finite filter tests equality of the permutation value and its input.", true),
            Def("c2", "Two-cycles", CycleCountFormula(true), "Section 6, page 4: \"If σ ∈ Sₙ, let c₁(σ) be the number of fixed points of σ and let c₂(σ) be the number of two-cycles in its cycle decomposition.\" Mathlib's cycleType omits fixed points and retains the other cycle lengths with multiplicity.", true),
            Def("chi", "The character", CharacterFormula(), "Section 6, page 4, (6.1): chi^(n−2,2)(σ) = binom(c1(σ),2) + c2(σ) − c1(σ). Each natural count is cast to the integers; the subtraction is integer subtraction.", true),
            Def("edgeSwap", "Edge transposition", SwapFormula(), "Section 6, page 4: \"Let τ_e = (ij) denote the transposition corresponding to an edge e = ij.\" Sym2.lift uses Equiv.swap_comm, so the transposition is independent of endpoint order.", true),
            Def("M_r2", "Edge-word moment", MomentFormula(), "Section 6, page 4, (6.2): M_r^(2)(G) is the sum over all edge words (e₁,…,e_r) of chi(τ_e₁⋯τ_e_r). List.ofFn lists indices in increasing order and List.prod preserves the displayed multiplication order. The definition uses this right side, as the source identifies it with the trace. The extension r = 0 is included in the evaluator; the inversion statement only uses r = 2, 3, 4.", true),
            Def("noIsolated", "No isolated vertices", NoIsolatedFormula(), "Every vertex has an adjacent vertex; the empty vertex carrier satisfies this condition."),
            Def("twoPoints", "Points in two-cycles", TwoPointsFormula(), "A point lies in the support of the permutation but not in the support of its square precisely when its orbit has length two."),
            Thm("twoPoints_card", "Counting points in two-cycles", TwoPointsCardFormula(), "Cycle induction separates a cycle of length two from every other nontrivial cycle. Disjoint products give disjoint unions of these point sets and additive cycle multiplicities."),
            Thm("N_H_of_enumeration", "Enumerating support counts", EnumerationFormula(false), "An injective enumeration of all r-edge subsets rewrites the support count as a sum of isomorphism indicators, provided H has r edges."),
            Thm("counts_eq_of_iso_enumerations", "Matched support enumerations", EnumerationFormula(true), "Two injective exhaustive enumerations paired by endpoint-graph isomorphisms give equal counts for every r-edge model H."),
            Def("digit", "Radix digit", DigitFormula(), "Nat.div is integer quotient and Nat.mod is the remainder, including Lean's total conventions at base zero."),
            Def("pack", "Packing radix digits", PackFormula(), "Nat.ofDigits reads the finite digit list in little-endian order."),
            Thm("digit_pack", "Decoding a bounded digit", DigitPackFormula(), "For positive base and digits below the base, integer quotient and remainder recover each digit at an index below the packed length."),
            Def("endpointIso_image", "Endpoint isomorphism from relabelling", EndpointIsoFormula(), "The image hypothesis transports endpoint membership. The isomorphism sends each endpoint vertex v to q(v), using q.subtypeEquiv; its adjacency proof is the membership transport for unordered pairs."),
            Def("countNat", "Counting a Boolean predicate", CountNatFormula(), "Filter the natural numbers below n, then take the list length."),
            Def("natChi", "Character on a natural-number action", NatCharacterFormula(), "The displayed expression is the literal body of natChi. The two local counts test fixed points and nonfixed points fixed by the square. Dividing the latter by two uses Nat.div; both counts and the quotient are cast to integers."),
            Def("natProd", "Word action on natural numbers", NatProdFormula(), "The list head acts after the tail, matching multiplication of permutations."),
            Def("evalMoment", "Recursive edge-word evaluator", EvalFormula(), "At depth zero evaluate the accumulated word. At positive depth append each edge once and sum the recursive values. Repeated edges and all edge orders are included."),
            Thm("evalMoment_sound", "Soundness of the evaluator", EvalSoundFormula(), "Induction on the remaining word length identifies the recursive sum with the sum over functions Fin r → Fin m. Natural-number actions agree with the corresponding permutations on Fin n, including repeated or equal endpoints."),
            Thm("evalMoment_two_fin", "Two-prefix decomposition", TwoFinFormula(), "Two applications of the evaluator recursion expose the first two edge choices as finite sums, leaving the remaining r choices recursive."),
            Def("wordMoment", "Moment indexed by an edge enumeration", WordMomentFormula(), "The index function chooses unordered edges; the list of their transpositions has length r and is multiplied in increasing index order."),
            Thm("moment_reindex", "Reindexing graph edge words", ReindexFormula(), "An injective exhaustive edge enumeration supplies an equivalence with the graph's edge subtype. The induced equivalence on word functions reindexes the finite sum.")), []));
    private static DocumentBlock Def(string name, string title, Formula formula, string prose, bool literature = false) =>
        Describe.Lean(DescribeId.Create("shapiro-support-" + Safe(name).ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Thm(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("shapiro-support-" + Safe(name).ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static string Safe(string name) => name switch { "N_H" => "count", "c1" => "fixed", "c2" => "cycles", "chi" => "character", "M_r2" => "moment", _ => name.Replace('_', '-') };
    private static Formula n => F.Id("n");
    private static Formula h => F.Id("h");
    private static Formula g => F.Id("G");
    private static Formula s => F.Id("S");
    private static Formula sigma => F.Id("sigma");
    private static Formula Perm(Formula type) => App(Q("Equiv", "Perm"), type);
    private static Formula PermBind(Formula body) => All("n", Nat(), All("sigma", Perm(Fin(n)), body));
    private static Formula EndpointSetFormula() => All("n", Nat(), All("S", Edges(n), Equal(C("endpointSet", s), App(Q("Finset", "biUnion"), s, Q("Sym2", "toFinset")))));
    private static Formula EndpointGraphFormula() => All("n", Nat(), All("S", Edges(n), Equal(Endpoint(s), App(Q("SimpleGraph", "induce"), App(Q("SimpleGraph", "fromEdgeSet"), Cast(s, Call("Set", Call("Sym2", Fin(n))))), Cast(C("endpointSet", s), Call("Set", Fin(n)))))));
    private static Formula CountFormula()
    {
        Formula model = F.Id("H");
        Formula predicate = Lam("S", Edges(n), NonemptyIso(Endpoint(s), model));
        Formula filtered = App(Q("Finset", "filter"), predicate, App(Q("Finset", "powerset"), EdgeSet(g)));
        return All("n", Nat(), All("h", Nat(), All("G", Graph(n), All("H", Graph(h), Equal(C("NH", g, model), FinsetCard(filtered))))));
    }
    private static Formula CycleCountFormula(bool two)
    {
        Formula v = F.Id("v");
        Formula rhs = two ? App(Q("Multiset", "count"), D(2), App(Q("Equiv.Perm", "cycleType"), sigma))
            : FinsetCard(App(Q("Finset", "filter"), Lam("v", Fin(n), Equal(App(sigma, v), v)), Cast(Q("Finset", "univ"), Call("Finset", Fin(n)))));
        return PermBind(Equal(C(two ? "c2" : "c1", sigma), rhs));
    }
    private static Formula CharacterFormula() => PermBind(Equal(C("chi", sigma), Subtract(Add(Cast(App(Q("Nat", "choose"), C("c1", sigma), D(2)), Ints()), Cast(C("c2", sigma), Ints())), Cast(C("c1", sigma), Ints()))));
    private static Formula SwapFormula() => All("n", Nat(), Equal(Cast(C("edgeSwap"), Fn(Call("Sym2", Fin(n)), Perm(Fin(n)))), App(Q("Sym2", "lift"), Seq(Langle, Q("Equiv", "swap"), Comma, Sp, Q("Equiv", "swap_comm"), Rangle))));
    private static Formula MomentFormula()
    {
        Formula r = F.Id("r"), w = F.Id("w"), i = F.Id("i");
        Formula word = App(Q("List", "ofFn"), Lam("i", Fin(r), C("edgeSwap", Val(App(w, i)))));
        return All("n", Nat(), All("G", Graph(n), All("r", Nat(), Equal(C("Mr2", g, r), SumOver("w", Fn(Fin(r), EdgeSet(g)), C("chi", ListProd(word)))))));
    }
    private static Formula NoIsolatedFormula() => All("n", Nat(), All("G", Graph(n), IffFormula(C("noIsolated", g), All("v", Fin(n), Ex("w", Fin(n), App(Q("SimpleGraph", "Adj"), g, F.Id("v"), F.Id("w")))))));
    private static Formula AlphaBind(Formula body) => All("alpha", F.Id("Type"), Inst(Call("Fintype", F.Id("alpha")), Inst(Call("DecidableEq", F.Id("alpha")), All("sigma", Perm(F.Id("alpha")), body))));
    private static Formula TwoPointsFormula() => AlphaBind(Equal(C("twoPoints", sigma), App(Q("Finset", "sdiff"), App(Q("Equiv.Perm", "support"), sigma), App(Q("Equiv.Perm", "support"), new Formula.Power(sigma, D(2))))));
    private static Formula TwoPointsCardFormula() => AlphaBind(Equal(FinsetCard(C("twoPoints", sigma)), Multiply(D(2), App(Q("Multiset", "count"), D(2), App(Q("Equiv.Perm", "cycleType"), sigma)))));
    private static Formula EnumerationFormula(bool paired)
    {
        Formula r = F.Id("r"), t = F.Id("t"), a = F.Id("a"), b = F.Id("b"), gp = F.Id("Gprime"), model = F.Id("H"), i = F.Id("i");
        Formula type = Fn(Fin(t), Edges(n));
        Formula result = paired ? Equal(C("NH", g, model), C("NH", gp, model)) : Equal(C("NH", g, model), SumOver("i", Fin(t), Call("ite", NonemptyIso(Endpoint(App(a, i)), model), D(1), D(0))));
        result = Implies(Equal(FinsetCard(EdgeSet(model)), r), result);
        if (paired) result = Implies(All("i", Fin(t), Iso(Endpoint(App(a, i)), Endpoint(App(b, i)))), result);
        Formula Exhaust(Formula e, Formula graph) => Equal(App(Q("Finset", "image"), e, Cast(Q("Finset", "univ"), Call("Finset", Fin(t)))), App(Q("Finset", "powersetCard"), r, EdgeSet(graph)));
        if (paired) result = Implies(Exhaust(b, gp), result);
        result = Implies(Exhaust(a, g), result);
        if (paired) result = Implies(App(Q("Function", "Injective"), b), result);
        result = Implies(App(Q("Function", "Injective"), a), result);
        if (paired) result = All("b", type, result);
        result = All("a", type, result);
        result = All("H", Graph(h), result);
        if (paired) result = All("Gprime", Graph(n), result);
        return All("n", Nat(), All("h", Nat(), All("r", Nat(), All("t", Nat(), All("G", Graph(n), result)))));
    }
    private static Formula DigitFormula() => All("b", Nat(), All("p", Nat(), All("i", Nat(), Equal(C("digit", F.Id("b"), F.Id("p"), F.Id("i")), App(Q("Nat", "mod"), App(Q("Nat", "div"), F.Id("p"), new Formula.Power(F.Id("b"), F.Id("i"))), F.Id("b"))))));
    private static Formula PackFormula() => All("b", Nat(), All("n", Nat(), All("f", Fn(Nat(), Nat()), Equal(C("pack", F.Id("b"), n, F.Id("f")), App(Q("Nat", "ofDigits"), F.Id("b"), ListMap(F.Id("f"), App(Q("List", "range"), n)))))));
    private static Formula DigitPackFormula()
    {
        Formula b = F.Id("b"), f = F.Id("f"), i = F.Id("i");
        return All("b", Nat(), All("n", Nat(), Implies(Less(D(0), b), All("f", Fn(Nat(), Nat()), Implies(All("j", Nat(), Implies(Less(F.Id("j"), n), Less(App(f, F.Id("j")), b))), All("i", Nat(), Implies(Less(i, n), Equal(C("digit", b, C("pack", b, n, f), i), App(f, i)))))))));
    }
    private static Formula EndpointIsoFormula()
    {
        Formula sp = F.Id("Sprime"), q = F.Id("q"), hq = F.Id("hq"), v = F.Id("v");
        Formula law = Equal(App(Q("Finset", "image"), App(Q("Sym2", "map"), q), s), sp);
        Formula iso = C("endpointIso_image", s, sp, q, hq);
        Formula type = Seq(iso, Sp, Colon, Sp, Iso(Endpoint(s), Endpoint(sp)));
        Formula value = All("v", Seq(OpenBrace, F.Id("x"), Sp, Colon, Sp, Fin(n), Sp, Bar, Sp, Member(F.Id("x"), C("endpointSet", s)), CloseBrace), Equal(Val(App(iso, v)), App(q, Val(v))));
        return All("n", Nat(), All("S", Edges(n), All("Sprime", Edges(n), All("q", Perm(Fin(n)), All("hq", law, And(type, value))))));
    }
    private static Formula CountNatFormula() => All("n", Nat(), All("p", Fn(Nat(), F.Id("Bool")), Equal(C("countNat", n, F.Id("p")), App(Q("List", "length"), App(Q("List", "filter"), F.Id("p"), App(Q("List", "range"), n))))));
    private static Formula NatCharacterFormula()
    {
        Formula p = F.Id("p"), v = F.Id("v");
        Formula c = C("countNat", n, Lam("v", Nat(), App(Q("BEq", "beq"), App(p, v), v)));
        Formula d = C("countNat", n, Lam("v", Nat(), App(Q("Bool", "and"), Call("bne", App(p, v), v), App(Q("BEq", "beq"), App(p, App(p, v)), v))));
        Formula rhs = Subtract(Add(Cast(App(Q("Nat", "choose"), c, D(2)), Ints()), Cast(App(Q("Nat", "div"), d, D(2)), Ints())), Cast(c, Ints()));
        return All("n", Nat(), All("p", Fn(Nat(), Nat()), Equal(C("natChi", n, p), rhs)));
    }

    private static Formula NatProdFormula()
    {
        Formula x = F.Id("x"), u = F.Id("u"), v = F.Id("v"), w = F.Id("w");
        return And(All("x", Nat(), Equal(C("natProd", EmptyList(), x), x)), All("u", Nat(), All("v", Nat(), All("w", Call("List", ProductType(Nat(), Nat())), All("x", Nat(), Equal(C("natProd", App(Q("List", "cons"), Pair(u, v), w), x), App(Q("Equiv", "swapCore"), u, v, C("natProd", w, x))))))));
    }
    private static Formula EvalFormula()
    {
        Formula edges = F.Id("edges"), r = F.Id("r"), w = F.Id("w"), e = F.Id("e");
        Formula pair = ProductType(Nat(), Nat()), list = Call("List", pair);
        Formula zero = Equal(C("evalMoment", n, edges, D(0), w), C("natChi", n, C("natProd", w)));
        Formula step = Equal(C("evalMoment", n, edges, Add(r, D(1)), w), App(Q("List", "sum"), ListMap(Lam("e", pair, C("evalMoment", n, edges, r, App(Q("List", "append"), w, Seq(OpenBracket, e, CloseBracket)))), edges)));
        return All("n", Nat(), All("edges", list, All("w", list, And(zero, All("r", Nat(), step)))));
    }
    private static Formula EvalSoundFormula()
    {
        Formula m = F.Id("m"), e = F.Id("e"), r = F.Id("r"), w = F.Id("w"), a = F.Id("a"), i = F.Id("i"), v = F.Id("v");
        Formula pair = ProductType(Fin(n), Fin(n));
        Formula fst(Formula x) => App(Q("Prod", "fst"), x);
        Formula snd(Formula x) => App(Q("Prod", "snd"), x);
        Formula natPair(Formula x) => Pair(Val(fst(x)), Val(snd(x)));
        Formula natEdges = ListMap(Lam("i", Fin(m), natPair(App(e, i))), App(Q("List", "finRange"), m));
        Formula natWord = ListMap(Lam("a", pair, natPair(a)), w);
        Formula prefix = ListProd(ListMap(Lam("a", pair, Swap(fst(a), snd(a))), w));
        Formula rest = ListProd(App(Q("List", "ofFn"), Lam("i", Fin(r), Swap(fst(App(e, App(v, i))), snd(App(e, App(v, i)))))));
        return All("n", Nat(), All("m", Nat(), All("e", Fn(Fin(m), pair), All("r", Nat(), All("w", Call("List", pair), Equal(C("evalMoment", n, natEdges, r, natWord), SumOver("v", Fn(Fin(r), Fin(m)), C("chi", Multiply(prefix, rest)))))))));
    }
    private static Formula TwoFinFormula()
    {
        Formula m = F.Id("m"), e = F.Id("e"), r = F.Id("r"), w = F.Id("w"), i = F.Id("i"), j = F.Id("j");
        Formula pair = ProductType(Nat(), Nat()), list = Call("List", pair);
        Formula edges = ListMap(e, App(Q("List", "finRange"), m));
        return All("n", Nat(), All("m", Nat(), All("e", Fn(Fin(m), pair), All("r", Nat(), All("w", list, Equal(C("evalMoment", n, edges, Add(r, D(2)), w), SumOver("i", Fin(m), SumOver("j", Fin(m), C("evalMoment", n, edges, r, App(Q("List", "append"), w, Seq(OpenBracket, App(e, i), Comma, Sp, App(e, j), CloseBracket)))))))))));
    }
    private static Formula WordMomentFormula()
    {
        Formula m = F.Id("m"), e = F.Id("e"), r = F.Id("r"), w = F.Id("w"), i = F.Id("i");
        return All("n", Nat(), All("m", Nat(), All("e", Fn(Fin(m), Call("Sym2", Fin(n))), All("r", Nat(), Equal(C("wordMoment", e, r), SumOver("w", Fn(Fin(r), Fin(m)), C("chi", ListProd(App(Q("List", "ofFn"), Lam("i", Fin(r), C("edgeSwap", App(e, App(w, i)))))))))))));
    }
    private static Formula ReindexFormula()
    {
        Formula m = F.Id("m"), e = F.Id("e"), r = F.Id("r");
        return All("n", Nat(), All("m", Nat(), All("G", Graph(n), All("e", Fn(Fin(m), Call("Sym2", Fin(n))), Implies(Equal(App(Q("Finset", "image"), e, Cast(Q("Finset", "univ"), Call("Finset", Fin(m)))), EdgeSet(g)), Implies(App(Q("Function", "Injective"), e), All("r", Nat(), Equal(C("Mr2", g, r), C("wordMoment", e, r)))))))));
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Inst(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula IffFormula(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(Seq(Lex(owner), Dot, Lex(name))));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Field(Formula value, string name) => App(Q("SimpleGraph", name), value);
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints() => new Formula.Integers();
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Graph(Formula n) => Call("SimpleGraph", Fin(n));
    private static Formula Edges(Formula n) => Call("Finset", Call("Sym2", Fin(n)));
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula ProductType(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);

    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Sum, Underscore, Grp(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Parenthesized(body)));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));

    private static Formula Name(string name) => name switch
    {
        "c1" => F.Id("c1"),
        "c2" => F.Id("c2"),
        "chi" => F.Id("chi"),
        "NH" => Seq(F.Id("N"), Underscore, Grp(F.Id("H"))),
        "Mr2" => Seq(F.Id("M"), Underscore, Grp(F.Id("r2"))),
        "P5" => F.Id("P5"),
        _ => Lex(name),
    };
    private static Formula C(string name, params Formula[] args) => args.Length == 0 ? Name(name) : App(Name(name), args);
    private static Formula Iso(Formula a, Formula b) => Seq(a, Sp, Equiv, Underscore, Grp(F.Id("g")), Sp, b);
    private static Formula NonemptyIso(Formula a, Formula b) => Call("Nonempty", Parenthesized(Iso(a, b)));
    private static Formula FinsetCard(Formula s) => App(Q("Finset", "card"), s);
    private static Formula EdgeSet(Formula g) => Field(g, "edgeFinset");
    private static Formula Endpoint(Formula s) => C("endpointGraph", s);
    private static Formula Swap(Formula a, Formula b) => App(Q("Equiv", "swap"), a, b);
    private static Formula ListProd(Formula w) => App(Q("List", "prod"), w);
    private static Formula ListMap(Formula f, Formula w) => App(Q("List", "map"), f, w);
    private static Formula EmptyList() => Seq(OpenBracket, CloseBracket);
    private static Formula Lex(string name) => name switch
    {
        "natChi" => F.Id("natChi"),
        "Equiv.Perm" => Seq(F.Id("Equiv"), Dot, F.Id("Perm")),
        "endpointIso_image" => Seq(F.Id("endpointIso"), Underscore, Grp(F.Id("image"))),
        "swap_comm" => Seq(F.Id("swap"), Underscore, Grp(F.Id("comm"))),
        _ => F.Id(name),
    };
}
